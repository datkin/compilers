structure RegAlloc : REG_ALLOC =
struct

structure Frame = MipsFrame

type allocation = Frame.register Temp.Table.table

fun rewrite (instrs, spills) =
    (* TODO:
     * 1. Perform spill coalescing?
     * 2. alloc local for spill
     * 3. rewrite uses *)
    raise Fail "Spilling not yet implemented"

fun alloc (instrs, frame) =
    let
      val (flowgraph, nodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveout) = Liveness.interferenceGraph flowgraph

      (* TODO: define a better spill heuristic. *)

      val (allocation, spills) = Color.color {interference = igraph,
                                                 initial = Frame.tempMap,
                                                 spillCost = fn _ => 1,
                                                 registers = Frame.registers}
    in
      if List.null spills then
        (instrs, allocation)
      else
        alloc (rewrite (instrs, spills), frame)
    end

end
