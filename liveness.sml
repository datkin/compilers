structure TempSet = RedBlackSetFn (struct
                                   type ord_key = Temp.temp
                                   val compare = Int.compare
                                   end)

structure Liveness :
sig
  datatype igraph =
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node -> Temp.temp,
               moves: (Graph.node * Graph.node) list}

  val livenessGraph :
      Flow.flowgraph -> TempSet.set Flow.Graph.Table.table *
                        TempSet.set Flow.Graph.Table.table

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

fun listToSet list = TempSet.addList (TempSet.empty, list)

fun livenessGraph (Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      (* Initialize an empty live map as a base *)
      val initLiveMap = foldr (fn (n, t) => FT.enter (t, n, TempSet.empty))
                              FT.empty
                              nodes

      fun tablesEqual (t1, t2) =
          (* We assume that nodes[t1] = nodes[t2] *)
          (* This really just pulls the TempSets for each node
           * from each table and compares them to see if they've changed *)
          List.all (fn node =>
                       let
                         val set1 = FT.get (t1, node, "set1")
                         val set2 = FT.get (t2, node, "set2")
                       in
                         TempSet.compare (set1, set2) = General.EQUAL
                       end)
                   nodes

      fun fix eq f x =
          let val x' = f x in
            if eq (x, x') then x' else fix eq f x'
          end

      fun build (node, (liveIn, liveOut)) =
          let
            val nodeOut = FT.get (liveOut, node, "out[n]")
            val useSet = listToSet (FT.get (use, node, "use[n]"))
            val defSet = listToSet (FT.get (def, node, "def[n]"))
            val nodeIn' = TempSet.union (useSet,
                                         TempSet.difference (nodeOut,
                                                             defSet))
            val liveIn' = FT.enter (liveIn, node, nodeIn')

            val nodeOut' = foldr TempSet.union
                                 TempSet.empty
                                 (map (fn s => FT.get (liveIn, s, "in[s]"))
                                      (Flow.Graph.succ node))
            val liveOut' = FT.enter (liveOut, node, nodeOut')
          in
            (liveIn', liveOut')
          end

      val (liveIn, liveOut) = fix (fn ((li, lo), (li', lo')) =>
                                      tablesEqual (li, li') andalso
                                      tablesEqual (lo, lo'))
                                  (fn (liveIn, liveOut) =>
                                      foldr build
                                            (liveIn, liveOut)
                                            nodes)
                                  (initLiveMap, initLiveMap)
    in
      (liveIn, liveOut)
    end

fun interferenceGraph (flowgraph as Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      val (_, liveOutMap) = livenessGraph flowgraph

      val allTemps = foldr (fn (node, temps) =>
                               let
                                 val defs = listToSet (FT.get (def, node, "def[n]"))
                                 val uses = listToSet (FT.get (use, node, "use[n]"))
                               in
                                 TempSet.union (temps, TempSet.union (defs, uses))
                               end)
                           TempSet.empty
                           nodes

      val allTemps = TempSet.listItems allTemps

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
      fun liveOut node = TempSet.listItems (FT.get (liveOutMap, node, "live-out[n]"))

      (* WTF!!!! This should be so much more elegant just
       * traversing the instr list for Assem.MOVE instructions *)
      fun getMoves (node, moves) =
          if FT.get (ismove, node, "ismove[n]") then
            let
              val [dst] = FT.get (def, node, "def[n]")
              val [src] = FT.get (use, node, "use[n]")
              val dstNode = tempToNode dst
              val srcNode = tempToNode src
            in
              app (fn b => if src <> b then
                             Graph.mk_edge {from=dstNode,
                                            to=tempToNode b}
                           else ())
                  (liveOut node);
              (dstNode, srcNode) :: moves
            end
          else
            moves

      val moves = foldr getMoves [] nodes

      fun addEdges node =
          if not (FT.get (ismove, node, "ismove[n]")) then
            app (fn a =>
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
               moves=[]},
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
