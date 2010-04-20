structure MakeGraph: sig
  val instrs2graph: Assem.instr list -> Flow.flowgraph * Flow.Graph.node list
end = struct
  fun instrs2graph instrs =
      let
        val graph = Graph.newGraph ()

        val nodes = map (fn _ => Graph.newNode graph) instrs

        val label2node = List.mapPartial
                           (fn (Assem.LABEL {assem, lab}, node) => SOME (lab, node)
                             | (_, _) => NONE)
                           (ListPair.zip (instrs, nodes))

        fun findLabelNode label =
            case List.find (fn (label', node) => label = label') label2node of
                 SOME (_, node) => SOME node
               | NONE => NONE

        fun linkEdges (Assem.OPER {assem, dst, src, jump=SOME jumps}, node, _) =
             (app (fn label =>
                      case findLabelNode label of
                           SOME jump => Graph.mk_edge {from=node, to=jump}
                         (* External call or jump out of function. Ignore. *)
                         | NONE => ())
                      (* | NONE => (if isSome next then
                                      Graph.mk_edge {from=node,
                                                     to=valOf next}
                                    else ()) *)
                  jumps;
              SOME node)
          | linkEdges (_, node, SOME next) =
             (Graph.mk_edge {from=node, to=next}; SOME node)
          | linkEdges (_, node, NONE) = SOME node

        val _ = ListPair.foldr linkEdges NONE (instrs, nodes)

        fun buildTables (Assem.OPER {assem, dst, src, jump}, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, Temp.Set.fromList dst),
             Graph.Table.enter (uses, node, Temp.Set.fromList src),
             Graph.Table.enter (moves, node, false))
          | buildTables (Assem.MOVE {assem, dst, src}, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, Temp.Set.singleton dst),
             Graph.Table.enter (uses, node, Temp.Set.singleton src),
             Graph.Table.enter (moves, node, true))
          | buildTables (Assem.LABEL _, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, Temp.Set.empty),
             Graph.Table.enter (uses, node, Temp.Set.empty),
             Graph.Table.enter (moves, node, false))

        val (defTable, useTable, moveTable) = ListPair.foldl
                                              buildTables
                                              (Graph.Table.empty,
                                               Graph.Table.empty,
                                               Graph.Table.empty)
                                              (instrs, nodes)
      in
        (Flow.FGRAPH {control=graph,
                      def=defTable,
                      use=useTable,
                      ismove=moveTable},
         nodes)
      end
end


