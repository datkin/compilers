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

type liveSet = TempSet.set

structure T = Flow.Graph.Table
type liveMap = liveSet T.table

datatype igraph = IGRAPH of {graph: Graph.graph,
                             tnode: Temp.temp -> Graph.node,
                             gtemp: Graph.node -> Temp.temp,
                             moves: (Graph.node * Graph.node) list}

fun listToSet list =
    TempSet.addList (TempSet.empty, list)

fun forceLookF (table, key, errorStr) =
    case Flow.Graph.Table.look (table, key) of
      SOME value => value
    | NONE => ErrorMsg.impossible (errorStr ^ " not found")

fun forceLookT (table, key, errorStr) =
    case Temp.Table.look (table, key) of
      SOME value => value
    | NONE => ErrorMsg.impossible (errorStr ^ " not found")

fun livenessGraph (Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      val liveIn = foldr (fn (n, t) => T.enter (t, n, TempSet.empty))
                         T.empty
                         nodes
      val liveOut = foldr (fn (n, t) => T.enter (t, n, TempSet.empty))
                          T.empty
                          nodes

      fun tablesEqual (t1, t2) =
          (* We assume that nodes[t1] = nodes[t2] *)
          (* This really just pulls the TempSets for each node
           * from each table and compares them to see if they've changed *)
          List.all (fn node =>
                       let
                         val set1 = forceLookF (t1, node, "set1")
                         val set2 = forceLookF (t2, node, "set2")
                       in
                         TempSet.compare (set1, set2) = General.EQUAL
                       end)
                   nodes

      fun fix f (x, y) =
          let
            val (x', y') = f (x, y)
          in
            if tablesEqual (x, x') andalso
               tablesEqual (y, y') then
              (x', y')
            else
              fix f (x', y')
          end

      fun build (node, (liveIn, liveOut)) =
          let
            val nodeOut = forceLookF (liveOut, node, "out[n]")
            val useSet = listToSet (forceLookF (use, node, "use[n]"))
            val defSet = listToSet (forceLookF (def, node, "def[n]"))
            val nodeIn' = TempSet.union (useSet,
                                        TempSet.difference (nodeOut,
                                                            defSet))
            val liveIn' = T.enter (liveIn, node, nodeIn')

            val nodeOut' = foldr
                             TempSet.union
                             TempSet.empty
                             (map (fn s => forceLookF (liveIn, s, "in[s]"))
                                  (Flow.Graph.succ node))

            val liveOut' = T.enter (liveOut, node, nodeOut')
          in
            (liveIn', liveOut')
          end

      val (liveIn, liveOut) = fix (fn (liveIn, liveOut) =>
                                      foldr build
                                            (liveIn, liveOut)
                                            nodes)
                                  (liveIn, liveOut)
    in
      (liveIn, liveOut)
    end

fun interferenceGraph (flowgraph as Flow.FGRAPH {control, def, use, ismove}) =
    let
      val nodes = Flow.Graph.nodes control
      val (liveIn, liveOut) = livenessGraph flowgraph

      val allTemps = foldr (fn (node, temps) =>
                               let
                                 val defs = listToSet (forceLookF (def, node, "def[n]"))
                                 val uses = listToSet (forceLookF (use, node, "use[n]"))
                               in
                                 TempSet.union (temps,
                                                TempSet.union (defs, uses))
                               end)
                           TempSet.empty
                           nodes
      val allTemps = TempSet.listItems allTemps

      val igraph = Graph.newGraph ();

      val (nodeToTemp, tempToNode) =
          foldr (fn (temp, (n2t, t2n)) =>
                    let val node = Graph.newNode igraph in
                      (Graph.Table.enter (n2t, node, temp),
                       Temp.Table.enter (t2n, temp, node))
                    end)
                (Graph.Table.empty, Temp.Table.empty)
                allTemps

      fun tempToNodeFn temp = forceLookT (tempToNode, temp, "temp->node")
      fun nodeToTempFn node = forceLookF (nodeToTemp, node, "node->temp")
      fun liveOutFn node =
          TempSet.listItems (forceLookF (liveOut, node, "live-out[n]"))

      (* WTF!!!! This should be so much more elegant just
       * traversing the instr list for Assem.MOVE instructions *)
      fun getMoves (node, moves) =
          if forceLookF (ismove, node, "ismove[n]") then
            let
              val [dst] = forceLookF (def, node, "def[n]")
              val [src] = forceLookF (use, node, "use[n]")
              val dstNode = tempToNodeFn dst
              val srcNode = tempToNodeFn src
            in
              app (fn b => if src <> b then
                             Graph.mk_edge {from=dstNode,
                                            to=tempToNodeFn b}
                           else ())
                  (TempSet.listItems (forceLookF (liveOut,
                                                  node,
                                                  "live-out[n]")));
              (dstNode, srcNode) :: moves
            end
          else
            moves

      val moves = foldr getMoves [] nodes

      fun addEdges node =
          if not (forceLookF (ismove, node, "ismove[n]")) then
            app (fn a =>
                    let val aNode = tempToNodeFn a in
                      app (fn b =>
                              if a <> b then
                                Graph.mk_edge {from=aNode,
                                               to=tempToNodeFn b}
                              else ())
                          (liveOutFn node)
                    end)
                (forceLookF (def, node, "def[n]"))
          else ()

      val _ = app addEdges nodes
    in
      (IGRAPH {graph=igraph,
               tnode=tempToNodeFn,
               gtemp=nodeToTempFn,
               moves=[]},
       liveOutFn)
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

(* Doesn't work here. :'(
      fun fix f x =
          let val x' = f x in
            if x' = x then x' else fix f x'
          end
*)
