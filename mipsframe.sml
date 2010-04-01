structure MipsFrame :> FRAME =
struct
  structure T = Tree

  val numArgTemps = 4
  val FP = Temp.newTemp ()
  val RV = Temp.newTemp ()
  val ARGS = List.tabulate (numArgTemps, (fn _ => Temp.newTemp ()))
  val wordSize = 4

  datatype access = InFrame of int | InReg of Temp.temp
  type frame = {formals: access list, localCount: int ref,
                name: Temp.label, frameOffset: int ref}

  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

  fun allocFormal (escapes, (accesses, i, frameOffset)) =
    if i < numArgTemps then
      (* These args are passed via the argument registers (a0 - a3).
       * Those that escape are copied into locals *below* the frame pointer.
       * Those that don't escape are copied into registers. *)
      (if escapes then
         (InFrame frameOffset :: accesses, i+1, frameOffset - wordSize)
       else
         (InReg (Temp.newTemp ()) :: accesses, i+1, frameOffset))
    else
      (* All arguments after the first 4 are passed by the caller, on the stack
       * *above* the frame pointer. They are pushed by the caller from right to
       * left, making the last argument the furthest one from the frame pointer. *)
      (InFrame ((i - numArgTemps + 1) * wordSize) :: accesses, i+1, frameOffset)

  fun newFrame {name, formals} =
    let
      val (formals, _, frameOffset) = (foldl allocFormal ([], 0, 0) formals)
    in
      {name = name, formals = (rev formals),
       localCount = ref 0, frameOffset = ref frameOffset}
    end

  fun name (f: frame) = #name f
  fun formals (f: frame) = #formals f

  fun allocLocal (frame: frame) true =
        let
          val localCount = #localCount frame
          val frameOffset = #frameOffset frame
        in
          (localCount := !localCount + 1;
           frameOffset := !frameOffset - wordSize;
           InFrame (!frameOffset))
        end
    | allocLocal frame false =
        let
          val localCount = #localCount frame
        in
          (localCount := !localCount + 1;
           InReg (Temp.newTemp ()))
        end

  fun externalCall (name, args) =
    T.CALL (T.NAME (Temp.namedLabel name), args)

  fun exp (InFrame offset) fpExp = T.MEM (T.BINOP (T.PLUS, T.CONST offset, fpExp))
    | exp (InReg temp) _         = T.TEMP temp

  fun seq [] = T.EXP (T.CONST 0)
    | seq [exp] = exp
    | seq (exp :: exps) = (T.SEQ (exp, (seq exps)))

  fun procEntryExit1 (frame, body) =
  let
    val funFormals = formals frame
    fun moveArg (argTemp, access) =
      T.MOVE (exp access (T.TEMP FP), T.TEMP argTemp)
    val viewShift = seq (ListPair.map moveArg (ARGS, funFormals))
  in
    case funFormals of
         [] => body
       | _  => T.SEQ (viewShift, body)
  end

end
