structure RegAlloc : REG_ALLOC =
struct

structure Frame = MipsFrame

type allocation = Frame.register Temp.Table.table

fun eq a b = a = b

fun rewrite (instrs, frame, spills) =
    (* TODO:
     * 1. Perform spill coalescing?
     * 2. alloc local for spill
     * 3. rewrite uses *)
    let
      fun spill (temp, instrs) =
          let
            val access = Frame.allocLocal frame true
            val accessExp = Frame.exp access (Tree.TEMP Frame.FP)

            fun moveInsn (dst, src) =
                MipsGen.codegen frame (Tree.MOVE (dst, src))

            fun storeInsn temp = moveInsn (accessExp, Tree.TEMP temp)

            fun fetchInsn temp = moveInsn (Tree.TEMP temp, accessExp)

            fun replace newTemp temp' =
                if temp = temp' then newTemp else temp'

            fun transform insnBuilder temps =
                if List.exists (eq temp) temps then
                  let val newTemp = Temp.newTemp () in
                    (insnBuilder newTemp,
                     map (replace newTemp) temps)
                  end
                else
                  ([], temps)

            fun rewriteInsn (Assem.OPER {assem, dst, src, jump}) =
                let
                  val (pre, src') = transform fetchInsn src
                  val (post, dst') = transform storeInsn dst
                in
                  pre @ [Assem.OPER {assem=assem,
                                     dst=dst',
                                     src=src',
                                     jump=jump}] @ post
                end
              | rewriteInsn (Assem.MOVE {assem, src, dst}) =
                let
                  val (pre, [src']) = transform fetchInsn [src]
                  val (post, [dst']) = transform storeInsn [dst]
                in
                  pre @ [Assem.MOVE {assem=assem,
                                     dst=dst',
                                     src=src'}] @ post
                end
              | rewriteInsn instr = [instr]
          in
            foldl (fn (instr, instrs) =>
                      instrs @ (rewriteInsn instr))
                  []
                  instrs
          end
    in
      (* Fold over all the instrs. At each use, generate a fetch
       * and re-write the temp used in the use.
       * For a def, rewrite the def'd temp and then generate a
       * write. *)
      foldl spill instrs spills
    end

fun alloc (instrs, frame) =
    let
      val (flowgraph, nodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveout) = Liveness.interferenceGraph flowgraph

      val Flow.FGRAPH {control, def, use, ismove} = flowgraph

(*
      val _ = Flow.show flowgraph
      val _ = app (fn node =>
                      print (Graph.nodename node ^ ": " ^
                             String.concatWith ", "
                                               (map Frame.tempToRegister
                                                    (liveout node)) ^
                             "\n"))
                  nodes
 *)

      val Liveness.IGRAPH {graph, tnode, gtemp, moves} = igraph
      (* val _ = Liveness.show (TextIO.stdOut, igraph) *)

      (* Use (defs + uses) / degree, ie, the spill cost is low if the
       * temp is accessed a low number of times but interferes with a
       * large number of other temps. *)
      fun spillCost node =
          let
            val temp = gtemp node

            fun getOccurences node =
                let
                  val uses = Graph.Table.get (use, node, "use[n]")
                  val defs = Graph.Table.get (def, node, "def[n]")
                  val useCount = if Temp.Set.member (uses, temp) then 1 else 0
                  val defCount = if Temp.Set.member (defs, temp) then 1 else 0
                in
                  useCount + defCount
                end

            val occurences = foldl (fn (node, total) =>
                                       getOccurences node + total)
                                   0
                                   nodes

            val degree = length (Graph.adj node)
          in
            Real./ (Real.fromInt occurences, Real.fromInt degree)
          end

      val (allocation, spills) = Color.color {interference = igraph,
                                              initial = Frame.tempMap,
                                              spillCost = spillCost,
                                              registers = Frame.registers}
    in
      if List.null spills then
        (instrs, frame, allocation)
      else
        alloc (rewrite (instrs, frame, spills), frame)
    end

end
