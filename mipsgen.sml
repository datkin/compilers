(* TODO: make this type opaque *)
structure MipsGen : CODEGEN =
struct
structure A = Assem and T = Tree
structure Frame = MipsFrame
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
           * right operand against zero *)
          case relop of
            T.EQ => SOME "beqz"
          | T.NE => SOME "bnez"
          | T.LT => SOME "bgtz"
          | T.LE => SOME "bgez"
          | T.GT => SOME "bltz"
          | T.GE => SOME "blez"
          | _ => NONE
      fun getR0Branch relop =
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
      fun munchStm (T.SEQ (s1, s2)) =
          (munchStm s1; munchStm s2)

        | munchStm (T.LABEL label) =
          emit (A.LABEL {assem=Symbol.name label ^ ":",
                         lab=label})

        | munchStm (T.JUMP (T.NAME label, _)) =
          emit (A.OPER {assem="b `j0", (* difference from j `j0? *)
                        dst=[], src=[],
                        jump=SOME [label]})
        | munchStm (T.JUMP (exp, labels)) =
          emit (A.OPER {assem="jr `s0",
                        dst=[],
                        src=[munchExp exp],
                        jump=SOME labels})

          (* False label is the fallthrough *)
        | munchStm (T.CJUMP (relop, T.CONST 0, e, l1, l2)) =
          (case getL0Branch relop of
             SOME insn =>
             emit (A.OPER {assem=insn ^ " `s0, `j0",
                           dst=[],
                           src=[munchExp e],
                           jump=SOME [l1, l2]})
           | NONE =>
             emit (A.OPER {assem=(getBranch relop) ^ " $zero, `s0, `j0",
                           dst=[],
                           (* TODO: zero register? *)
                           src=[(*Frame.ZERO,*) munchExp e],
                           jump=SOME [l1, l2]}))
        | munchStm (T.CJUMP (relop, e, T.CONST 0, l1, l2)) =
          (case getR0Branch relop of
             SOME insn =>
             emit (A.OPER {assem=insn ^ " `s0, `j0",
                           dst=[],
                           src=[munchExp e],
                           jump=SOME [l1, l2]})
           | NONE =>
             emit (A.OPER {assem=(getBranch relop) ^ " `s0, $zero, `j0",
                           dst=[],
                           (* TODO: zero register? *)
                           src=[(*Frame.ZERO,*) munchExp e],
                           jump=SOME [l1, l2]}))
        | munchStm (T.CJUMP (relop, e1, e2, l1, l2)) =
          emit (A.OPER {assem=(getBranch relop) ^ " `s0, `s1, `j0",
                        dst=[],
                        src=[munchExp e1, munchExp e2],
                        jump=SOME [l1, l2]})

        | munchStm (T.MOVE (T.TEMP r, T.CONST n)) =
          emit (A.OPER {assem="li `d0, " ^ (Int.toString n),
                        dst=[r], src=[], jump=NONE})
        | munchStm (T.MOVE (T.TEMP r,
                            T.MEM (T.BINOP (T.PLUS,
                                            T.CONST n,
                                            T.TEMP s)))) =
          emit (A.OPER {assem="lw `d0, " ^ (Int.toString n) ^ "(`s0)",
                        dst=[r], src=[s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP r,
                            T.MEM (T.BINOP (T.PLUS,
                                            T.TEMP s,
                                            T.CONST n)))) =
          emit (A.OPER {assem="lw `d0, " ^ (Int.toString n) ^ "(`s0)",
                        dst=[r], src=[s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP r,
                            T.MEM (T.BINOP (T.MINUS,
                                            T.TEMP s,
                                            T.CONST n)))) =
          emit (A.OPER {assem="lw `d0, " ^ (Int.toString (~n)) ^ "(`s0)",
                        dst=[r], src=[s], jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, T.NAME label)) =
          emit (A.OPER {assem="la `d0, " ^ (Symbol.name label),
                        dst=[r], src=[], jump=NONE})
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST n, T.TEMP r)),
                            e)) =
          emit (A.OPER {assem="sw `s0, " ^ (Int.toString n) ^ "(`d0)",
                        dst=[r],
                        src=[munchExp e],
                        jump=NONE})
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.TEMP r, T.CONST n)),
                              e)) =
          emit (A.OPER {assem="sw `s0, " ^ (Int.toString n) ^ "(`d0)",
                        dst=[r],
                        src=[munchExp e],
                        jump=NONE})
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.MINUS, T.TEMP r, T.CONST n)),
                              e)) =
          emit (A.OPER {assem="sw `s0, " ^ (Int.toString (~n)) ^ "(`d0)",
                        dst=[r],
                        src=[munchExp e],
                        jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.PLUS, T.CONST n, e)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.PLUS, e, T.CONST n)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.MINUS, T.CONST 0, e)))) =
                    emit (A.OPER {assem="neg `d0, `s0",
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.AND, T.CONST n, e)))) =
                    emit (A.OPER {assem="andi `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.AND, e, T.CONST n)))) =
                    emit (A.OPER {assem="andi `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.OR, T.CONST n, e)))) =
                    emit (A.OPER {assem="ori `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.OR, e, T.CONST n)))) =
                    emit (A.OPER {assem="ori `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.LSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="sll `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.RSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="srl `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.ARSHIFT, e, T.CONST n)))) =
                    emit (A.OPER {assem="sra `d0, `s0, " ^ (Int.toString n),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (T.MINUS, e, T.CONST n)))) =
                    emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString (~n)),
                                  dst=[r],
                                  src=[munchExp e],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, (T.BINOP (binop, e1, e2)))) =
                    emit (A.OPER {assem=(getBinop binop) ^ " `d0, `s0, `s1",
                                  dst=[r],
                                  src=[munchExp e1, munchExp e2],
                                  jump=NONE})
        | munchStm (T.MOVE (T.TEMP r, e)) =
          emit (A.MOVE {assem="move `d0, `s0",
                        dst=r,
                        src=munchExp e})
        | munchStm (T.MOVE (T.MEM dExp, sExp)) =
          (* Any semantics about which should eval first? *)
          emit (A.OPER {assem="sw `s0, (`d0)",
                        dst=[munchExp dExp],
                        src=[munchExp sExp],
                        jump=NONE})
        | munchStm (T.MOVE _) = ErrorMsg.impossible "Moving to non temp/mem"

        | munchStm (T.EXP exp) =
          (munchExp exp; ())

      (* We assume exprs have already been constant folded
       * by the IR generator. Although procEntryExitN, and
       * munchArg code will generate some unfolded IR. *)
      and munchExp (T.BINOP (T.PLUS, T.CONST n, e)) =
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.PLUS, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString n),
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
                     emit (A.OPER {assem="andi `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.AND, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="andi `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.OR, T.CONST n, e)) =
          result (fn r =>
                     emit (A.OPER {assem="ori `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.OR, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="ori `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.LSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="sll `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.RSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="srl `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.ARSHIFT, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="sra `d0, `s0, " ^ (Int.toString n),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (T.MINUS, e, T.CONST n)) =
          result (fn r =>
                     emit (A.OPER {assem="addi `d0, `s0, " ^ (Int.toString (~n)),
                                   dst=[r],
                                   src=[munchExp e],
                                   jump=NONE}))
        | munchExp (T.BINOP (binop, e1, e2)) =
          result (fn r =>
                     emit (A.OPER {assem=(getBinop binop) ^ " `d0, `s0, `s1",
                                   dst=[r],
                                   src=[munchExp e1, munchExp e2],
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
                     emit (A.OPER {assem="li `d0, " ^ (Int.toString n),
                                   dst=[r], src=[], jump=NONE}))

        | munchExp (T.CALL (exp, args)) =
          let
            (* Caller saves *)
            val saves = map (fn _ => Temp.newTemp ()) Frame.callersaves
            (* Args *)
            val numArgTemps = length Frame.argregs
            val registerArgs = if length args > numArgTemps then
                                  List.take (args, numArgTemps)
                                else
                                  args
            val stackArgs = if length args > numArgTemps then
                              List.drop (args, numArgTemps)
                            else
                              []
            val srcs = ListPair.map (fn (tmp, exp) =>
                                        (munchStm (T.MOVE (T.TEMP tmp,
                                                           exp));
                                         tmp))
                                    (Frame.argregs, registerArgs)
            fun pushStackArg (exp, i) =
                (munchStm (T.MOVE (T.MEM (T.BINOP (T.MINUS,
                                                   T.TEMP Frame.SP,
                                                   T.CONST (i * Frame.wordSize))),
                                   exp));
                 i+1)
            val numStackArgs = foldr pushStackArg 0 stackArgs

            fun updateSp i =
                munchStm (T.MOVE (T.TEMP Frame.SP,
                                  T.BINOP (T.MINUS,
                                           T.TEMP Frame.SP,
                                           T.CONST (Frame.wordSize * i))))
          in
            updateSp numStackArgs;
            ListPair.map (fn (temp, callerSave) =>
                             munchStm (T.MOVE (T.TEMP temp,
                                               T.TEMP callerSave)))
                         (saves, Frame.callersaves);
            emit (callIsntr (exp, srcs));
            (* Caller restores *)
            ListPair.map (fn (callerSave, temp) =>
                             munchStm (T.MOVE (T.TEMP callerSave,
                                               T.TEMP temp)))
                         (Frame.callersaves, saves);
            updateSp (~numStackArgs);
            Frame.RV
          end

      and callIsntr (T.NAME label, srcs) =
          A.OPER {assem="jal `j0",
                  dst=[Frame.RA, Frame.RV] @ Frame.callersaves,
                  src=srcs,
                  jump=SOME [label]}
        | callIsntr (exp, srcs) =
          A.OPER {assem="jalr `s0",
                  dst=[Frame.RA, Frame.RV] @ Frame.callersaves,
                  src=[munchExp exp] @ srcs,
                  jump=NONE}
    in
      munchStm stm;
      rev (!ilist)
    end

end
