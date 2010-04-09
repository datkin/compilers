structure Tiger =
struct

fun withOpenFile name f =
    let
      val out = TextIO.openOut name
    in
      (f out before TextIO.closeOut out)
      handle e => (TextIO.closeOut out; raise e)
    end

structure Frame = Frame

fun emitProc out (frame, instr) =
    let
      val {prolog, body=instr, epilog} = Frame.procEntryExit3 (frame, instr)
      val format0 = Assem.format Frame.tempToRegister
    in
      TextIO.output (out, prolog);
      (* should be .text for mips, with .globl main *)
      app (fn i => TextIO.output (out, (format0 i)))
          instr;
      TextIO.output (out, epilog)
    end

fun emitStr out (label, str) =
    TextIO.output (out, Frame.string (label, str))

fun genInstr {body, frame} =
    let
      val stms = Canon.linearize body
      val stms' = Canon.traceSchedule (Canon.basicBlocks stms)
      val instrs = List.concat (map (MipsGen.codegen frame) stms')
      val instrs' = Frame.procEntryExit2 (frame, instrs)
    in
      instrs'
    end

fun rewriteProc (frame, instrs) : (Frame.frame * Assem.instr list) =
    let
      val (flowgraph, nodes) = MakeGraph.instrs2graph instrs
      val (igraph, liveout) = Liveness.interferenceGraph flowgraph
      (* TODO: Perform register allocation here *)
    in
      (frame, instrs)
    end

(* TODO: we can remove labels that are never referenced from anywhere. *)
(* We can also find jumps to jumps and rewrite them? *)
fun compile (name, source) =
    let
      val _ = (ErrorMsg.reset name; Translate.reset ())

      val ast = Parse.parse (name, source)
      (* Short circuit compilation on parse errors. *)
      val _ = if !ErrorMsg.anyErrors then
                (app ErrorMsg.display (!ErrorMsg.errorLog);
                 raise Fail "Compilation failed with parsing errors")
              else ()

      val _ = FindEscape.findEscape ast
      val {frags, ty} = Semant.transProg ast
      val _ = if !ErrorMsg.anyErrors then
                (app ErrorMsg.display (!ErrorMsg.errorLog);
                 raise Fail "Compilation failed with static errors")
              else ()

      fun partitionFrags (Frame.PROC proc, (procs, strs)) =
          (proc :: procs, strs)
        | partitionFrags (Frame.STRING str, (procs, strs)) =
          (procs, str :: strs)
      val (procs, strs) = foldr partitionFrags ([], []) frags

      val procInstrs = map (fn (proc as {body, frame}) =>
                               (frame, genInstr proc))
                           procs

      (* do register allocation and rewrite (spill) the instrs as necessary *)
      val procInstrs' = map rewriteProc procInstrs

      val _ = withOpenFile (name ^ ".s")
                           (fn out =>
                               (TextIO.output (out, "\t.data\n");
                                (app (emitStr out) strs);
                                TextIO.output (out, "\n\t.text\n");
                                TextIO.output (out, "\t.globl main\n");
                                (app (emitProc out) procInstrs)))
     in
      (procs, strs)
     end


fun compileFile filename = compile (filename, TextIO.openIn filename)

fun compileStr str = compile ("string", TextIO.openString str)
end
