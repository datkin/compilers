structure Liveness :
sig
  datatype igraph =
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node -> Temp.temp,
               moves: (Graph.node * Graph.node) list}

  val livenessGraph :
      Flow.flowgraph -> Temp.Set.set Flow.Graph.Table.table *
                        Temp.Set.set Flow.Graph.Table.table

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

(* Can this be cleaned up to look nicer/more concise?
 * Also, would it be possible to turn this into a fold
 * type function so that we can, e.g. do live-out creation
 * while doing the traversal, rather than doing the
 * traversal *and* then folding up over the returned list?
 * This sounds similar to the deforestation optimizations
 * that Wadler writes about. *)
fun topologicalSort nodes =
    let
      val mark = foldr (fn (n, t) => FT.enter (t, n, false))
                       FT.empty
                       nodes
      fun DFS (node, mark) =
          if not (FT.get (mark, node, "mark[i]")) then
            let
              val (nodes', mark') =
                  foldr (fn (n, (l, m)) =>
                            let val (l', m') = DFS (n, m) in
                              (l' @ l, m')
                            end)
                        ([], FT.enter (mark, node, true))
                        (Graph.pred node)
            in
              (node :: nodes', mark')
            end
          else ([], mark)
    in
      #1 (DFS (List.last nodes, mark))
    end

(* Create a depth-first tree and fold *down* the tree from the top.
 * It's tail recursive! kinda... *)
type node = Graph.node
fun foldroot (children: node -> node list)
             (continue: node -> bool) (* determine if we should continue *)
             (fold: node * 'a -> 'a)
             (base: 'a)
             (root: node) : 'a =
    let
      fun fold' (node, (acc, visited)) =
          if not (continue node) orelse
             isSome (FT.look (visited, node)) then
            (acc, visited)
          else
            foldl fold'
                  (fold (node, acc), FT.enter (visited, node, ()))
                  (children node)
      val (result, _) = fold' (root, (base, FT.empty))
    in
      result
    end

(* fun foldleaves children continue fold combine base root = ... *)

fun livenessGraph (Flow.FGRAPH {control, def, use, ismove}) =
    let
      (* We can topologically sort the nodes, but it turns out that
       * just traversing the nodes in reverse order (w/ foldr)
       * is actually slightly faster than sorting them first.
       * Topologically sorting only seems to save ~1 iteration. *)
      val nodes = (* topologicalSort *) (Flow.Graph.nodes control)

      (* Initialize an empty live map as a base *)
      val initLiveMap = foldr (fn (n, t) => FT.enter (t, n, Temp.Set.empty))
                              FT.empty
                              nodes

      fun tablesEqual (t1, t2) =
          (* We assume that nodes[t1] = nodes[t2] *)
          (* This really just pulls the temp sets for each node
           * from each table and compares them to see if they've changed *)
          List.all (fn node =>
                       let
                         val set1 = FT.get (t1, node, "set1")
                         val set2 = FT.get (t2, node, "set2")
                       in
                         Temp.Set.compare (set1, set2) = General.EQUAL
                       end)
                   nodes

      fun fix eq f x n =
          let val x' = f x in
            if eq (x, x') then (x', n) else fix eq f x' (n+1)
          end

      fun build (node, (liveIn, liveOut)) =
          let
            val nodeOut = FT.get (liveOut, node, "out[n]")
            val useSet = FT.get (use, node, "use[n]")
            val defSet = FT.get (def, node, "def[n]")
            val nodeIn' = Temp.Set.union (useSet,
                                         Temp.Set.difference (nodeOut,
                                                             defSet))
            val liveIn' = FT.enter (liveIn, node, nodeIn')

            val nodeOut' = foldr Temp.Set.union
                                 Temp.Set.empty
                                 (map (fn s => FT.get (liveIn, s, "in[s]"))
                                      (Flow.Graph.succ node))
            val liveOut' = FT.enter (liveOut, node, nodeOut')
          in
            (liveIn', liveOut')
          end

      val ((liveIn, liveOut), n) = fix (fn ((li, lo), (li', lo')) =>
                                      tablesEqual (li, li') andalso
                                      tablesEqual (lo, lo'))
                                  (fn (liveIn, liveOut) =>
                                      foldr build
                                            (liveIn, liveOut)
                                            nodes)
                                  (initLiveMap, initLiveMap)
                                  0
(*
      val _ = print ("length: " ^ (Int.toString (length nodes)) ^ "\n")
      val _ = print ("its: " ^ (Int.toString n) ^ "\n")
 *)
    in
      (liveIn, liveOut)
    end

fun interferenceGraph (flowgraph as Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      val (_, liveOutMap) = livenessGraph flowgraph

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
      fun liveOut node = Temp.Set.listItems (FT.get (liveOutMap, node, "live-out[n]"))

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
                  (liveOut node);
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
                                   (liveOut node)
                             end)
                         (FT.get (def, node, "def[n]"))
          else ()

      val _ = app addEdges nodes
    in
      (IGRAPH {graph=igraph,
               tnode=tempToNode,
               gtemp=nodeToTemp,
               moves=moves},
       liveOut)
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
