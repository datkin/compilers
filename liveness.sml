structure Liveness :
sig
  datatype igraph =
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node -> Temp.temp,
               moves: (Graph.node * Graph.node) list}

  val interferenceGraph :
      Flow.flowgraph -> igraph * (Flow.Graph.node -> Temp.temp list)

  val show : TextIO.outstream * igraph -> unit
end =
struct

structure FT = Flow.Graph.Table

datatype igraph = IGRAPH of {graph: Graph.graph,
                             tnode: Temp.temp -> Graph.node,
                             gtemp: Graph.node -> Temp.temp,
                             moves: (Graph.node * Graph.node) list}

(* Create a depth-first tree and fold *down* the tree from the root.
 * The stop function is used to determine if folding over the
 * current branch of the tree should terminate "early" on the given
 * node. Note that the node will still be "folded over". The
 * children function generates a list of nodes to visit next. The
 * signature is tailored for use in other folds (see below).
 * It's tail recursive! kinda... *)
(* (node -> bool) ->
 * (node -> node list) ->
 * (node * 'a -> 'a) ->
 * (node * 'a) -> 'a *)
fun foldroot stop children fold (root, base) =
    let
      fun fold' (node, (acc, visited)) =
          if isSome (FT.look (visited, node)) then
            (acc, visited)
          else if stop node then
            (fold (node, acc), visited)
          else
            foldl fold'
                  (fold (node, acc), FT.enter (visited, node, ()))
                  (children node)

      val (result, _) = fold' (root, (base, FT.empty))
    in
      result
    end

fun topologicalSort root =
    foldroot (fn _ => false) Graph.succ op:: (root, [])

fun liveout (Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes as first :: _ = Flow.Graph.nodes control
      (* The topological sort returns one of the "deepest" nodes first,
       * we'll use that node as the starting point for liveness analysis. *)
      val sorted as last :: _ = topologicalSort first

      (* Initialize a map where every node's liveout set is empty. *)
      (* TODO: We should only have to init the nodes in sorted. Why
       * does build end up traversing nodes not in the sorted set? *)
      val base = foldr (fn (n, t) => FT.enter (t, n, Temp.Set.empty))
                              FT.empty
                              nodes

      fun build (root, liveout) =
          let
            (*   Given a temp used at the root node, find all the nodes from
             * which control flows into the root node. Traverse the flow-
             * graph in reverse, starting at these nodes, marking the temp
             * as live-out at each node, until a def of the given temp is
             * encountered.
             *   The def node will be the *last* node at which the temp is
             * marked live-out.
             *   It is important that we start this traversal at the nodes
             * which flow into the root, and not at the root itself, b/c
             * our stop heuristic would cause marking to terminate
             * immediately if the temp has already been marked live-out
             * at the root (e.g., if the temp is in the node's use *and*
             * def sets). *)
            fun markNodes (temp, liveout) =
                let
                  (* Keep traversing nodes unless:
                   * - the temp gets (re)defined at this node
                   * or
                   * - the temp is already marked live-out at this node. *)
                  fun toDefs node =
                      (Temp.Set.member (FT.get (def, node, "def[n]"),
                                        temp)
                       orelse
                       (Temp.Set.member (FT.get (liveout, node, "out[n]"),
                                         temp)))

                  (* Add the temp to this node's live-out set. *)
                  fun add (node, liveout') =
                      let val nodeout = FT.get (liveout', node, "out'[n]") in
                        FT.enter (liveout', node, Temp.Set.add (nodeout, temp))
                      end

                  (* Create a function to do the marking... *)
                  val marker = foldroot toDefs Graph.pred add
                in
                  (* ...and apply it to all the root's predecessors. *)
                  foldl marker liveout (Graph.pred root)
                end
          in
            (* For each temp used by this node, mark the temp as live-out
             * in all the nodes upstream of this one in the control-flow
             * graph. *)
            Temp.Set.foldl markNodes
                           liveout
                           (FT.get (use, root, "use[n]"))
          end
    in
      (* Apply the liveout-builder in reverse all the way up the flow graph.
       * By starting at (one of) the "deepest" nodes, we should minimize
       * the runtime. Once a temp has been marked live out on a node, we
       * don't need to visit that node again. This should result in each
       * node being visit once or never per temp. O(N * T), where N is the
       * number of nodes and T is the number of temps.
       * See: Appel pp 216 ("One variable at a time") *)
      foldroot (fn _ => false) Graph.pred build (last, base)
    end

fun interferenceGraph (flowgraph as Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      val liveoutMap = liveout flowgraph

      (* TODO: collect these from the liveoutmap? *)
      val allTemps = foldr (fn (node, temps) =>
                               let
                                 val defs = FT.get (def, node, "def[n]")
                                 val uses = FT.get (use, node, "use[n]")
                               in
                                 Temp.Set.union (temps, Temp.Set.union (defs, uses))
                               end)
                           Temp.Set.empty
                           nodes

      val allTemps = Temp.Set.listItems allTemps

      val igraph = Graph.newGraph ();

      val (nodeToTempMap, tempToNodeMap) =
          foldr (fn (temp, (n2t, t2n)) =>
                    let val node = Graph.newNode igraph in
                      (Graph.Table.enter (n2t, node, temp),
                       Temp.Table.enter (t2n, temp, node))
                    end)
                (Graph.Table.empty, Temp.Table.empty)
                allTemps

      (* Turn table accesses into functions *)
      fun tempToNode temp = Temp.Table.get (tempToNodeMap, temp, "temp->node")
      fun nodeToTemp node = FT.get (nodeToTempMap, node, "node->temp")
      fun liveout node = Temp.Set.listItems (FT.get (liveoutMap, node, "live-out[n]"))

      (* This should be so much more elegant just
       * traversing the instr list for Assem.MOVE instructions *)
      fun getMoves (node, moves) =
          if FT.get (ismove, node, "ismove[n]") then
            let
              val [dst] = Temp.Set.listItems (FT.get (def, node, "def[n]"))
              val [src] = Temp.Set.listItems (FT.get (use, node, "use[n]"))
              val dstNode = tempToNode dst
              val srcNode = tempToNode src
            in
              app (fn b => if not (src = b orelse dst = b) then
                             Graph.mk_edge {from=dstNode,
                                            to=tempToNode b}
                           else ())
                  (liveout node);
              (dstNode, srcNode) :: moves
            end
          else
            moves

      val moves = foldr getMoves [] nodes

      (* This only adds edges between dsts and live-outs (see: Appel 222)
       * however, there are some cases where this might not add nodes for
       * interfering nodes. For non move nodes, there should be edges
       * between all (live out temps unioned with all dst temps).
       * However, consider this case:
       *
       *     instr      liveout
       * L1:            a0, a1, a2
       *     c <- a0    a1, a2
       *     ...        ...
       *
       * Only c -> a1 and c -> a2 edges will be added. The fact that
       * a0, a1, and a2 interfere with each other at the label is not
       * recorded by this addEdges implementation. No interference edges
       * will be added to a0. Unioning the dsts
       * with the live-outs and adding edges between each of them at
       * every node would solve this problem, but I believe that we can
       * simply ignore the problem b/c it will be dealt with in the
       * register allocator by the precolored registers. Ie, in this
       * example, a0, a1 and a2 are precolored and will interfere
       * implicitly.
       * Another solution is to prefix each function with a "sink"
       * instruction that lists fp, a0-a3, etc as dst registers so they'll
       * all be marked as interfering (ie, in procEntryExit2). *)
      fun addEdges node =
          if not (FT.get (ismove, node, "ismove[n]")) then
            Temp.Set.app (fn a =>
                             let val aNode = tempToNode a in
                               app (fn b =>
                                       if a <> b then
                                         Graph.mk_edge {from=aNode,
                                                        to=tempToNode b}
                                       else ())
                                   (liveout node)
                             end)
                         (FT.get (def, node, "def[n]"))
          else ()

      val _ = app addEdges nodes
    in
      (IGRAPH {graph=igraph,
               tnode=tempToNode,
               gtemp=nodeToTemp,
               moves=moves},
       liveout)
    end

fun show (out, (IGRAPH {graph, tnode, gtemp, moves})) =
    let
      fun nodeToStr node = Int.toString (gtemp node)
      fun printNeighbors node =
          TextIO.output (out,
                         ((nodeToStr node) ^ ": " ^
                          String.concatWith ", "
                                            (map nodeToStr
                                                 (Graph.adj node))
                          ^ "\n"))
    in
      app printNeighbors (Graph.nodes graph)
    end

end
