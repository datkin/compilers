(* TODO: make this type opaque *)

(* TODO: the following program generates a label with no newline:
 * Tiger.compileStr "for i := 1 to 5 do (if i < 5 then break else 1; ())";
 * (this is b/c we don't place newlines after *any* labels) *)
structure MipsGen : CODEGEN =
struct

structure A = Assem and T = Tree
structure Frame = MipsFrame

fun const n = if n >= 0 then Int.toString n else "-" ^ Int.toString(~n)

fun codegen frame stm =
    let
      val ilist = ref (nil: A.instr list)
      fun emit x = ilist := x :: (!ilist)
      fun result gen =
          let val t = Temp.newTemp () in
            gen t; t
          end

      fun getBranch relop =
          case relop of
            T.EQ => "beq"
          | T.NE => "bne"
          | T.LT => "blt"
          | T.LE => "ble"
          | T.GT => "bgt"
          | T.GE => "bge"
          | T.ULT => "bltu"
          | T.ULE => "bleu"
          | T.UGT => "bgtu"
          | T.UGE => "bgeu"

      fun getL0Branch relop =
          (* Special case operators for comparing the
           * right operand against a zero on the left *)
          case relop of
            T.EQ => SOME "beqz"
          | T.NE => SOME "bnez"
          | T.LT => SOME "bgtz"
          | T.LE => SOME "bgez"
          | T.GT => SOME "bltz"
          | T.GE => SOME "blez"
          | _ => NONE

      fun getR0Branch relop =
          (* Special case operators for comparing the
           * left operand against a zero on the right *)
          case relop of
            T.EQ => SOME "beqz"
          | T.NE => SOME "bnez"
          | T.LE => SOME "blez"
          | T.LT => SOME "bltz"
          | T.GT => SOME "bgtz"
          | T.GE => SOME "bgez"
          | _ => NONE

      fun getBinop binop =
          (* assumes both operands are registers *)
          case binop of
            T.PLUS => "add"
          | T.MINUS => "sub"
          | T.MUL => "mul"
          | T.DIV => "div"
          | T.AND => "and"
          | T.OR => "or"
          | T.LSHIFT => "sllv"
          | T.RSHIFT => "srlv"
          | T.ARSHIFT => "srav"
          | T.XOR => "xor"

        (* Sequences *)
      fun munchStm (T.SEQ (s1, s2)) =
          (munchStm s1; munchStm s2)

        (* Labels *)
        | munchStm (T.LABEL label) =
          emit (A.LABEL {assem=Symbol.name label ^ ":",
                         lab=label})

        (* Jumps (unconditional) *)
        | munchStm (T.JUMP (T.NAME label, _)) =
          (* How does "j `j0" differ from "b `j0"? *)
          emit (A.OPER {assem="j `j0",
                        dst=[], src=[],
                        jump=SOME [label]})
        | munchStm (T.JUMP (exp, labels)) =
          emit (A.OPER {assem="jr `s0",
                        dst=[],
                        src=[munchExp exp],
                        jump=SOME labels})

        (* Branch instructions *)
        (* False label is the fallthrough *)
        | munchStm (T.CJUMP (relop, T.CONST 0, e, l1, l2)) =
          (case getL0Branch relop of
             SOME insn =>
             emit (A.OPER {assem=insn ^ " `s0, `j0",
                           dst=[],
                           src=[munchExp e],
                           jump=SOME [l1, l2]})
           | NONE =>
             emit (A.OPER {assem=(getBranch relop) ^ " `s0, `s1, `j0",
                           dst=[],
                           src=[Frame.ZERO, munchExp e],
                           jump=SOME [l1, l2]}))
        | munchStm (T.CJUMP (relop, e, T.CONST 0, l1, l2)) =
          (case getR0Branch relop of
             SOME insn =>
             emit (A.OPER {assem=insn ^ " `s0, `j0",
                           dst=[],
                           src=[munchExp e],
                           jump=SOME [l1, l2]})
           | NONE =>
             emit (A.OPER {assem=(getBranch relop) ^ " `s0, `s1, `j0",
                           dst=[],
                           src=[munchExp e, Frame.ZERO],
                           jump=SOME [l1, l2]}))
        | munchStm (T.CJUMP (relop, e1, e2, l1, l2)) =
          emit (A.OPER {assem=(getBranch relop) ^ " `s0, `s1, `j0",
                        dst=[],
                        src=[munchExp e1, munchExp e2],
                        jump=SOME [l1, l2]})

        (* Moves may either be to-memory or to-registers.
         * Thus all moves in the IR must have a left-hand
         * operand of T.MEM or T.TEMP. We will specifically
         * match a bunch of special cases for both types. *)

        (* Special case to-memory moves *)
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST n, d)),
                            e)) =
          emit (A.OPER {assem="sw `s0, " ^ const n ^ "(`s1)",
                        dst=[],
                        src=[munchExp e, munchExp d],
                        jump=NONE})
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, d, T.CONST n)),
                              e)) =
          emit (A.OPER {assem="sw `s0, " ^ const n ^ "(`s1)",
                        dst=[],
                        src=[munchExp e, munchExp d],
                        jump=NONE})
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.MINUS, d, T.CONST n)),
                              e)) =
          emit (A.OPER {assem="sw `s0, " ^ (const (~n)) ^ "(`s1)",
                        dst=[],
                        src=[munchExp e, munchExp d],
                        jump=NONE})

        (* Special case to-register moves *)
        | munchStm (T.MOVE (T.TEMP d, T.CONST n)) =
          emit (A.OPER {assem="li `d0, " ^ (const n),
                        dst=[d], src=[], jump=NONE})
        | munchStm (T.MOVE (T.TEMP d,
                            T.MEM (T.BINOP (T.PLUS,
                                            T.CONST n,
                                            s)))) =
          emit (A.OPER {assem="lw `d0, " ^ const n ^ "(`s0)",
                        dst=[d], src=[munchExp s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP d,
                            T.MEM (T.BINOP (T.PLUS,
                                            s,
                                            T.CONST n)))) =
          emit (A.OPER {assem="lw `d0, " ^ (const n) ^ "(`s0)",
                        dst=[d], src=[munchExp s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP d,
                            T.MEM (T.BINOP (T.MINUS,
                                            s,
                                            T.CONST n)))) =
          emit (A.OPER {assem="lw `d0, " ^ const (~n) ^ "(`s0)",
                        dst=[d], src=[munchExp s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, T.NAME label)) =
          emit (A.OPER {assem="la `d0, " ^ (Symbol.name label),
                        dst=[d], src=[], jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.PLUS, T.CONST n, e)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.PLUS, e, T.CONST n)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.MINUS, T.CONST 0, e)))) =
                    emit (A.OPER {assem="neg `d0, `s0",
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.AND, T.CONST n, e)))) =
                    emit (A.OPER {assem="andi `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.AND, e, T.CONST n)))) =
                    emit (A.OPER {assem="andi `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.OR, T.CONST n, e)))) =
                    emit (A.OPER {assem="ori `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.OR, e, T.CONST n)))) =
                    emit (A.OPER {assem="ori `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.LSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="sll `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.RSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="srl `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.ARSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="sra `d0, `s0, " ^ (const n),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (T.MINUS, e, T.CONST n)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (const (~n)),
                                  dst=[d],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP d, (T.BINOP (binop, e1, e2)))) =
                    emit (A.OPER {assem=(getBinop binop) ^ " `d0, `s0, `s1",
                                  dst=[d],
                                  src=[munchExp e1, munchExp e2],
                                  jump=NONE})

        (* Generic to-register move *)
        | munchStm (T.MOVE (T.TEMP d, e)) =
          emit (A.MOVE {assem="move `d0, `s0",
                        dst=d,
                        src=munchExp e})

        (* Generic to-memory move *)
        | munchStm (T.MOVE (T.MEM dExp, sExp)) =
          (* Any semantics about which should eval first? *)
          emit (A.OPER {assem="sw `s0, (`s1)",
                        dst=[],
                        src=[munchExp sExp, munchExp dExp],
                        jump=NONE})

        | munchStm (T.MOVE _) = ErrorMsg.impossible "Moving to non temp/mem"

        | munchStm (T.EXP exp) = (munchExp exp; ())

      (* We assume exprs have already been constant folded
       * by the IR generator. Although procEntryExitN, and
       * munchArg code will generate some unfolded IR. *)
      and munchExp (T.BINOP (T.PLUS, T.CONST n, e)) =
          (* Arithmetic expressions *)
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.PLUS, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.MINUS, T.CONST 0, e)) =
          result (fn r =>
                     emit (A.OPER {assem="neg `d0, `s0",
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.AND, T.CONST n, e)) =
          result (fn r =>
                     emit (A.OPER {assem="andi `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.AND, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="andi `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.OR, T.CONST n, e)) =
          result (fn r =>
                     emit (A.OPER {assem="ori `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.OR, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="ori `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.LSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="sll `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.RSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="srl `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.ARSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="sra `d0, `s0, " ^ (const n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.MINUS, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (const (~n)),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (binop, e1, e2)) =
          result (fn r =>
                     emit (A.OPER {assem=(getBinop binop) ^ " `d0, `s0, `s1",
                                   dst=[r],
                                   src=[munchExp e1, munchExp e2],
                                   jump=NONE}))

        (* Memory access *)
        | munchExp (T.MEM (T.BINOP (T.PLUS, e, T.CONST n))) =
          result (fn r =>
                     emit (A.OPER {assem="lw `d0, " ^ const n ^ "(`s0)",
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.MEM (T.BINOP (T.PLUS, T.CONST n, e))) =
          result (fn r =>
                     emit (A.OPER {assem="lw `d0, " ^ const n ^ "(`s0)",
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.MEM (T.BINOP (T.MINUS, e, T.CONST n))) =
          result (fn r =>
                     emit (A.OPER {assem="lw `d0, " ^ const (~n) ^ "(`s0)",
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
       | munchExp (T.MEM e) =
          result (fn r =>
                     emit (A.OPER {assem="lw `d0, (`s0)",
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))

        | munchExp (T.TEMP t) = t

        | munchExp (T.ESEQ (s, e)) = (munchStm s; munchExp e)

        | munchExp (T.NAME label) =
          result (fn r =>
                     emit (A.OPER {assem="la `d0, " ^ (Symbol.name label),
                                   dst=[r], src=[], jump=NONE}))

        | munchExp (T.CONST n) =
          result (fn r =>
                     emit (A.OPER {assem="li `d0, " ^ (const n),
                                   dst=[r], src=[], jump=NONE}))

        | munchExp (T.CALL (exp, args)) =
          let
            (* Generate temps for storing caller save registers. *)
            val saves = map (fn _ => Temp.newTemp ()) Frame.callersaves

            val numArgTemps = length Frame.argregs

            (* Extract the argument expressions that should be moved to arg registers *)
            val registerArgs = if length args > numArgTemps then
                                  List.take (args, numArgTemps)
                                else
                                  args

            (* Select only the arg registers actually being used. *)
            val srcs = ListPair.map (fn (_, argReg) => argReg)
                                    (registerArgs, Frame.argregs)

            (* Generate temps to store the arg registers in while the rest of the args are evaluated *)
            val registerArgTemps = map (fn _ => Temp.newTemp ()) registerArgs

            (* Extract the argument expressions that should be pushed to the stack *)
            val stackArgs = if length args > numArgTemps then
                              List.drop (args, numArgTemps)
                            else
                              []

            fun updateSp i =
                munchStm (T.MOVE (T.TEMP Frame.SP,
                                  T.BINOP (T.MINUS,
                                           T.TEMP Frame.SP,
                                           T.CONST (Frame.wordSize * i))))

            val numStackArgs = length stackArgs

            fun pushStackArg (exp, i) =
                (* Move the arg onto the stack.
                 * The stack space for the arg has *already* been
                 * allocated at this point, so we place args *above*
                 * the current stack pointer. *)
                (munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS,
                                                   T.TEMP Frame.SP,
                                                   T.CONST (i * Frame.wordSize))),
                                   exp));
                 (* Bump the stack pointer. We must do this incrementally,
                  * or else the stack pointer might be wonky if evaling one
                  * of the stack args involves calling another function.
                  * Of course we could solve this similar to register args and
                  * simply allocate a bunch of temps, eval the stack args to them
                  * and then copy them to the stack, but this increases register pressure.
                  * **Alternatively** can we bump the stack pointer ahead of time? *)
                 i+1)

          in
            (* Eval all the register args and copy them into temps.
             * We'll copy those temps to a0...a1 only after all the
             * args have been eval'd. *)
            ListPair.app (fn (tmp, exp) =>
                             munchStm (T.MOVE (T.TEMP tmp,
                                               exp)))
                         (registerArgTemps, registerArgs);

            (* Bump the stack pointer. We do this first b/c if evaling
             * the stack arguments involves pushing more intermediates
             * to the stack, it wont fuck with the existing items on the
             * stack. Basically, reserve the stack space *before* using it. *)
            updateSp numStackArgs;

            (* Push stack arguments. *)
            (* The last argument goes *furthest* from the stackpointer. *)
            foldl pushStackArg 1 stackArgs;

            (* Move copy the argument temps into the actual arg registers. *)
            ListPair.map (fn (argReg, argTmp) =>
                             munchStm (T.MOVE (T.TEMP argReg,
                                               T.TEMP argTmp)))
                         (Frame.argregs, registerArgTemps);
(* TODO: how does this affect register allocation?
            (* Copy the caller-save registers. *)
            ListPair.map (fn (temp, callerSave) =>
                             munchStm (T.MOVE (T.TEMP temp,
                                               T.TEMP callerSave)))
                         (saves, Frame.callersaves);
*)
            (* Emit the actual call instruction. *)
            emit (callInstr (exp, srcs));
(*
            (* Restore caller-save registers. *)
            ListPair.map (fn (callerSave, temp) =>
                             munchStm (T.MOVE (T.TEMP callerSave,
                                               T.TEMP temp)))
                         (Frame.callersaves, saves);
*)
            updateSp (~numStackArgs);

            Frame.RV
          end

      and callInstr (T.NAME label, srcs) =
          A.OPER {assem="jal " ^ Symbol.name label,
                  (* Registers that get written by the call
                   * (ie any register that is not preserved
                   *  across the call - if it's written and
                   *  restored we don't add it to this list)
                   * - Frame.RV
                   * - Caller-save registers
                   * - technically we could add the arg registers,
                   *   but they're dead after the call anyway.
                   * - *)
                  dst=[Frame.RV] @ Frame.callersaves @ Frame.argregs,
                  (* Registers that must be live at the call
                   * (ie that are read by the call):
                   * - a0 ... aN for arguments
                   * - Frame.SP for updating the frame pointer
                   * - Frame.RA for returning *)
                  src=srcs @ [Frame.SP],
                  (* Even though we *know* the label we're jumping to
                   * we don't emit it, b/c we don't want to create an
                   * edge in our control flow graph for this label.
                   * Instead, we use the dsts and the srcs to indicate
                   * what nodes ... *)
                  jump=NONE}
        | callInstr (exp, srcs) =
          A.OPER {assem="jalr `s0",
                  (* The callee may manipulate the arg registers and
                   * not restore them, so they need to interfere. *)
                  dst=[Frame.RV] @ Frame.callersaves @ Frame.argregs,
                  src=[munchExp exp, Frame.SP] @ srcs,
                  jump=NONE}
    in
      munchStm stm;
      rev (!ilist)
    end

end
