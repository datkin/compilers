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

fun emitProc out (Frame.PROC {body, frame}) =
    let
      val stms = Canon.linearize body
      val stms' = Canon.traceSchedule (Canon.basicBlocks stms)
      val instr = List.concat (map (MipsGen.codegen frame) stms')
      val instr = Frame.procEntryExit2 (frame, instr)
      val {prolog, body=instr, epilog} = Frame.procEntryExit3 (frame, instr)
      val format0 = Assem.format Frame.tempToRegister
    in
      TextIO.output (out, prolog);
      (* should be .text for mips, with .globl main *)
      app (fn i => TextIO.output (out, (format0 i)))
          instr;
      TextIO.output (out, epilog)
    end
    (* should be .data for mips *)
  | emitProc out (Frame.STRING (label, str)) =
    TextIO.output (out, Frame.string (label, str))

fun compile (name, source) =
    (ErrorMsg.reset name;
     Translate.reset ();
     let
       (* TODO: short circuit compilation on parse errors *)
       val ast = Parse.parse (name, source)
       val _ = FindEscape.findEscape ast
       val result as {frags, ty} = Semant.transProg ast
       fun split (proc as Frame.PROC _, (strs, procs)) = (strs, proc :: procs)
         | split (str as Frame.STRING _, (strs, procs)) = (str :: strs, procs)
       val (strFrags, procFrags) = foldr split ([], []) frags
     in
       if !ErrorMsg.anyErrors then
         (app ErrorMsg.display (!ErrorMsg.errorLog);
          raise Fail "Compilation failed")
       else
         let
           val _ = withOpenFile (name ^ ".s")
                                (fn out =>
                                    (TextIO.output (out, "\t.data\n");
                                     (app (emitProc out) strFrags);
                                     TextIO.output (out, "\n\t.text\n");
                                     TextIO.output (out, "\t.globl main\n");
                                     (app (emitProc out) procFrags)))
         in
           result
         end
     end)


fun compileFile filename = compile (filename, TextIO.openIn filename)

fun compileStr str = compile ("string", TextIO.openString str)
end
