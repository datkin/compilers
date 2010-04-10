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

type node = Graph.node

(* fold' creates a depth-first tree and fold *down* the tree from the root.
 * It's tail recursive! kinda... *)
fun folder (stop, children, fold) =
    let
      fun fold' (node, (acc, visited)) =
          if isSome (FT.look (visited, node)) then
            (acc, visited)
          else if stop node then
            (* Does this make sense? *)
            (fold (node, acc), visited)
          else
            foldl fold'
                  (fold (node, acc), FT.enter (visited, node, ()))
                  (children node)
    in
      fold'
    end

(* Applies the fold starting at the root node. *)
(* (stop: node -> bool,
    children: node -> node list,
    fold: node * 'a -> 'a,
    base: 'a, root: node) -> 'a *)
fun foldroot stop children fold base root =
    let
      val fold' = folder (stop, children, fold)
      val (result, _) = fold' (root, (base, FT.empty)) in
      result
    end

(* Applies the fold starting at the children of the root. *)
fun foldchildren stop children fold base root =
    let
      val fold' = folder (stop, children, fold)
      val (result, _) = foldl fold'
                              (base, FT.empty)
                              (children root)
    in
      result
    end

fun topologicalSort root =
    foldroot (fn _ => false) Graph.succ op:: [] root

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

      fun buildLiveout (root, liveout) =
          let
            (* Continue if the temp isn't already defined or part of
             * the liveout set for this node. *)
            fun toDefs temp node' =
                (Temp.Set.member (FT.get (def, node', "def[n]"),
                                  temp)
                 orelse
                 (Temp.Set.member (FT.get (liveout, node', "out[n]"),
                                   temp)))

            (* Add the temp to the liveout of this node. *)
            fun add temp (node', liveout') =
                let val nodeout = FT.get (liveout', node', "out'[n]") in
                  FT.enter (liveout', node', Temp.Set.add (nodeout, temp))
                end

          in
            (* For each temp defined at this node, walk backwards in
             * the control flow graph, marking the temp as live out,
             * until we arrive at *another* definition of the temp.
             * That node will be the *last* node of which it is live out. *)
            Temp.Set.foldl (fn (temp, liveout') =>
                               foldchildren (toDefs temp)
                                            Graph.pred
                                            (add temp)
                                            liveout'
                                            root)
                           liveout
                           (FT.get (use, root, "use[n]"))
          end
    in
      (* Apply the liveout-builder in reverse all the way up the flow graph.
       * By starting at (one of) the "deepest" nodes, we should minimize
       * the runtime. Once a temp has been marked live out on a node, we
       * don't need to visit that node again. This should result in each
       * node being visit once or never per temp.
       * See: Appel pp 216 ("One variable at a time") *)
      foldroot (fn _ => false) Graph.pred buildLiveout base last
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
