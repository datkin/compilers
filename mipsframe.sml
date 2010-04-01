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

  val SP = Temp.newTemp ()
  val RA = Temp.newTemp ()

  fun rewriteCall (exp, args) =
      let
        val returnLabel = Temp.newLabel ()
        val registerArgs = if length args > numArgTemps then
                             List.take (args, numArgTemps)
                           else
                             args
        val stackArgs = if length args > numArgTemps then
                          List.drop (args, numArgTemps)
                        else
                          []
        val (_, stackArgCode) =
            (List.foldr (fn (argExp, (stackPos, code)) =>
                            (stackPos + 1,
                             T.MOVE (T.MEM (T.BINOP (T.MINUS,
                                                     T.TEMP SP,
                                                     T.CONST (wordSize * stackPos))),
                                     argExp) :: code))
                        (0, [])
                        stackArgs)
      in
        T.ESEQ (seq ([(* Bump the SP two and save the current fp, ra *)
                      T.MOVE (T.TEMP SP, T.BINOP (T.MINUS,
                                                  T.TEMP SP,
                                                  T.CONST (wordSize * 2))),
                      T.MOVE (T.MEM (T.BINOP (T.PLUS,
                                              T.TEMP SP,
                                              T.CONST wordSize)),
                              T.TEMP FP),
                      T.MOVE (T.MEM (T.BINOP (T.PLUS,
                                              T.TEMP SP,
                                              T.CONST (wordSize * 2))),
                              T.TEMP RA)] @

                     (* Insn to bump the stack pointer needs to be the first thing
                      * in the fn *def*, not the call itself. *)
                     (* last stack arg at fp-4 *)
                     ListPair.map (fn (argExp, argTmp) => T.MOVE (T.TEMP argTmp,
                                                                  argExp))
                                  (registerArgs, ARGS) @
                     stackArgCode @
                     [T.MOVE (T.TEMP FP, T.BINOP (T.MINUS,
                                                  T.TEMP SP,
                                                  T.CONST (wordSize * (length stackArgs)))),
                      T.MOVE (T.TEMP RA, T.NAME returnLabel), (* jal insn *)
                      T.JUMP (exp, []),
                      T.LABEL returnLabel,
                      (* Retore FP, RA and the stack pointer *)
                      T.MOVE (T.TEMP FP, T.MEM (T.BINOP (T.PLUS,
                                                         T.TEMP SP,
                                                         T.CONST wordSize))),
                      T.MOVE (T.TEMP RA, T.MEM (T.BINOP (T.PLUS,
                                                         T.TEMP SP,
                                                         T.CONST (wordSize *2)))),
                      T.MOVE (T.TEMP SP, T.BINOP (T.PLUS,
                                                  T.TEMP SP,
                                                  T.CONST (wordSize * 2)))]),
                T.TEMP RV)
      end

  fun rewriteBody (body, frame) =
      let
        val argCount = length (formals frame)
        val stackArgCount = if argCount > numArgTemps then
                              argCount - numArgTemps
                            else
                              0
        val stackOffset = (stackArgCount * wordSize) + ~(!(#frameOffset frame))
      in
        seq [T.MOVE (T.TEMP SP, T.BINOP (T.MINUS,
                                         T.TEMP SP,
                                         T.CONST stackOffset)),
             body,
             T.MOVE (T.TEMP SP, T.BINOP (T.PLUS,
                                         T.TEMP SP,
                                         T.CONST stackOffset)),
             T.JUMP (T.TEMP RA, [])]
      end

end
