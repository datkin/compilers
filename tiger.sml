structure Tiger =
struct

structure CodeGen = MipsGen
structure Frame = MipsFrame

fun withOpenFile name f =
    let
      val out = TextIO.openOut name
    in
      (f out before TextIO.closeOut out)
      handle e => (TextIO.closeOut out; raise e)
    end

fun emitProc out (instr, frame, allocs) =
    let
      val {prolog, body=instr, epilog} = Frame.procEntryExit3 (frame, instr)
      val format0 = Assem.format allocs
      val instr' = List.filter (fn Assem.MOVE {assem, dst, src} =>
                                    allocs dst <> allocs src
                                 | _ => true)
                               instr

    in
      TextIO.output (out, prolog);
      (* should be .text for mips, with .globl main *)
      app (fn i => TextIO.output (out, (format0 i)))
          instr';
      TextIO.output (out, epilog)
    end

fun emitStr out (label, str) =
    TextIO.output (out, Frame.string (label, str))

fun genInstr {body, frame} =
    let
      val stms = Canon.linearize body
      val stms' = Canon.traceSchedule (Canon.basicBlocks stms)
      val instrs = List.concat (map (CodeGen.codegen frame) stms')
      val instrs' = Frame.procEntryExit2 (frame, instrs)
    in
      instrs'
    end

(* TODO: we can remove labels that are never referenced from anywhere. *)
(* We can also find jumps to jumps and rewrite them? *)
fun compile (name, source) =
    let
      val _ = (ErrorMsg.reset name; Translate.reset ())

      (* Short circuit compilation on parse errors. *)
      val ast = Parse.parse (name, source)
      val _ = if !ErrorMsg.anyErrors then
                (app ErrorMsg.display (!ErrorMsg.errorLog);
                 raise Fail "Compilation failed with parsing errors")
              else ()

      (* Short circuit compilation on semantic errors. *)
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
                               (genInstr proc, frame))
                           procs
(*
      val debugProcs = map (fn (instrs, frame) =>
                               (instrs, frame, Frame.tempToRegister))
                           procInstrs

      val _ = withOpenFile (name ^ ".s")
                           (fn out =>
                               (TextIO.output (out, "\t.data\n");
                                (app (emitStr out) strs);
                                TextIO.output (out, "\n\t.text\n");
                                TextIO.output (out, "\t.globl main\n");
                                (app (emitProc out) debugProcs)))
*)
      val allocedProcs = map RegAlloc.alloc procInstrs

      val allocedProcs = map (fn (a, b, allocs) =>
                                 (a, b, (fn t =>
                                            Temp.Table.get (allocs, t, "reg[t]"))))
                             allocedProcs

      val _ = withOpenFile (name ^ ".s")
                           (fn out =>
                               (TextIO.output (out, "\t.data\n");
                                (app (emitStr out) strs);
                                TextIO.output (out, "\n\t.text\n");
                                TextIO.output (out, "\t.globl main\n");
                                (app (emitProc out) allocedProcs)))

     in
      (frags, ty, procs, strs)
     end


fun compileFile filename = compile (filename, TextIO.openIn filename)

fun compileStr str = compile ("string", TextIO.openString str)
end
