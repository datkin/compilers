structure MipsFrame :> FRAME =
struct
  type register = string
  structure T = Tree

  val numArgTemps = 4
  val FP = Temp.newTemp ()
  val RV = Temp.newTemp ()
  val SP = Temp.newTemp ()
  val RA = Temp.newTemp ()
  val ZERO = Temp.newTemp ()

  val specialregs = [FP, RV, SP, RA, ZERO]
  val argregs = List.tabulate (numArgTemps, (fn _ => Temp.newTemp ()))
  val calleesaves = List.tabulate (8, (fn _ => Temp.newTemp ()))
  val callersaves = List.tabulate (10, (fn _ => Temp.newTemp()))

  fun labelRegisters label regs =
      let
        val (labels, _) =
            foldl (fn (r, (rs, n)) =>
                      ((r, label ^ Int.toString n) :: rs, n+1))
                  ([], 0)
                  regs
      in
        labels
      end

  val tempMap = foldr Temp.Table.enter' Temp.Table.empty
                      ([(FP, "fp"),
                        (RV, "rv"),
                        (SP, "sp"),
                        (RA, "ra"),
                        (ZERO, "zero")] @
                       labelRegisters "a" argregs @
                       labelRegisters "s" calleesaves @
                       labelRegisters "t" callersaves)

  fun tempToRegister temp =
      "$" ^ (case Temp.Table.look (tempMap, temp) of
               SOME register => register
             | NONE => Temp.toString temp)

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

  fun moveReg (reg, tmp) =
      T.MOVE (T.TEMP reg, T.TEMP tmp)

  (* TODO: we will implement a spilling register allocator,
   * so we are safe allocating temps for all the callee-save
   * registers. *)
  fun procEntryExit1 (frame, body) =
  let
    (* TODO: FP adjustment/restore is done outside of this code, by
     * procEntryExit3 (?) so we need somewhere else to save the old FP? *)
    val saved = [RA] @ calleesaves
    val temps = map (fn temp => Temp.newTemp ()) saved
    val registerSaves = seq (ListPair.mapEq moveReg (temps, saved))
    val registerRestores = seq (ListPair.mapEq moveReg (saved, temps))
    val body' = seq [registerSaves, body, registerRestores]

    fun moveArg (arg, access) =
      T.MOVE (exp access (T.TEMP FP), T.TEMP arg)
    val funFormals = formals frame
    val viewShift = seq (ListPair.map moveArg (argregs, funFormals))
  in
    case funFormals of
         [] => body'
       | _  => T.SEQ (viewShift, body')
  end

  fun procEntryExit2 (frame, instrs) =
      instrs @
      [Assem.OPER {assem="",
                   (* TODO: are these correct? *)
                   dst=[],
                  (* This indicates that these registers will be used as
                   * sources by instructions added in the final phase,
                   * procEntryExit3, see: Appel pp 209. *)
                   src=[RA, RV, SP, ZERO],
                   (* SOME [] here indicates that control does not
                    * flow to the next instruction, but rather that
                    * control will transfer to some unknown location
                    * at this point. *)
                   jump=SOME []}]

  fun procEntryExit3 (frame, body) =
      (* TODO: add sp allocation, fp adjustment *)
      {prolog= "\n" ^ Symbol.name (name frame) ^ ":\t# Procedure\n",
       body=body,
       (* TODO: restore sp, fp *)
       epilog="\tjr $ra # End\n"}

  fun string (label, str) =
       (* Ensure each word starts aligned on a word boundary.
        * (see: Hennessy & Patterson A-47) *)
      "\t.align 2\n" ^
      (Symbol.name label) ^ ":\t.word " ^ (Int.toString (String.size str)) ^ "\n" ^
      "\t.ascii \"" ^ str ^ "\"\n"

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
                                  (registerArgs, argregs) @
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

structure Frame = MipsFrame
