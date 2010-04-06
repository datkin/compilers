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
        fun link (Assem.OPER {assem, dst, src, jump=SOME jumps}, node, _) =
             (app (fn label =>
                      case findLabelNode label of
                           SOME next => Graph.mk_edge {from=node, to=next}
                         | NONE => (* External call. Ignore *) ())
                  jumps;
              SOME node)
          | link (_, node, SOME next) =
             (Graph.mk_edge {from=node, to=next}; SOME node)
          | link (_, node, NONE) = SOME node
        val _ = ListPair.foldr link NONE (instrs, nodes)
        fun bar (Assem.OPER {assem, dst, src, jump}, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, dst),
             Graph.Table.enter (uses, node, src),
             Graph.Table.enter (moves, node, false))
          | bar (Assem.MOVE {assem, dst, src}, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, [dst]),
             Graph.Table.enter (uses, node, [src]),
             Graph.Table.enter (moves, node, true))
          | bar (Assem.LABEL _, node, (defs, uses, moves)) =
            (Graph.Table.enter (defs, node, []),
             Graph.Table.enter (uses, node, []),
             Graph.Table.enter (moves, node, false))
        val (defTable, useTable, moveTable) = ListPair.foldl
                                              bar
                                              (Graph.Table.empty, Graph.Table.empty, Graph.Table.empty)
                                              (instrs, nodes)
      in
        (Flow.FGRAPH {control=graph,
                      def=defTable,
                      use=useTable,
                      ismove=moveTable},
         nodes)
      end
end


