signature TRANSLATE =
sig
  type exp
  type level
  type access
  type breakpoint
  structure Frame : FRAME

  val BOGUS : exp
  val UNIT : exp
  val NIL : exp

  val outermost : level
  val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access

  val simpleVar : access * level -> exp
  val fieldVar : exp * int -> exp
  val subscriptVar : exp * exp list * int -> exp

  val assign : exp * exp -> exp
  val sequence : exp list -> exp
  val whileExp : exp * exp * breakpoint -> exp
  val forExp : exp * exp * exp * exp * breakpoint -> exp
  val newBreakpoint : unit -> breakpoint
  val break : breakpoint -> exp
  val binop : Types.ty * exp * Absyn.oper * exp -> exp
  val ifExp : exp * exp * exp -> exp
  val callExp : Temp.label * exp list * level * level -> exp

  val recordExp : exp list -> exp
  val arrayExp : exp list * exp -> exp

  val intLit : int -> exp
  val stringLit : string -> exp

  val procEntryExit : {level: level, body: exp} -> unit

  val result : unit -> Frame.frag list
  val reset : unit -> unit
end

structure Translate :> TRANSLATE =
struct
  structure Frame = MipsFrame
  structure T = Tree and A = Absyn

  datatype exp = Ex of T.exp
               | Nx of T.stm
               | Cx of Temp.label * Temp.label -> T.stm
  datatype level = Top | Nested of {parent: level, frame: Frame.frame, id: unit ref}
  type access = level * Frame.access
  type breakpoint = Temp.label

  val BOGUS = Ex (T.CONST 555)
  val UNIT = Nx (T.EXP (T.CONST 666))
  val NIL = Ex (T.CONST 777)

  val frags = ref [] : Frame.frag list ref
  val outermost = Top

  fun newLevel {parent=parent as Nested _, name, formals} =
      Nested {parent=parent, frame=Frame.newFrame {name=name, formals=true :: formals}, id=ref ()}
    | newLevel {parent=Top, name, formals} =
      Nested {parent=Top, frame=Frame.newFrame {name=name, formals=formals}, id=ref ()}

  fun formals (level as (Nested {parent, frame, id})) =
      (case Frame.formals frame of
         [] => (ErrorMsg.impossible "Frame has no static link"; [])
       | _ :: formals => map (fn frameAccess => (level, frameAccess)) formals)
    | formals Top = []

  fun allocLocal (level as Nested {parent, frame, id}) escapes = (level, Frame.allocLocal frame escapes)
    | allocLocal Top _ = ErrorMsg.impossible "Attempted to allocate in the outermost frame."

  fun seq [] = T.EXP (T.CONST 222)
    | seq [stm1] = stm1
    | seq (stm :: stms) = T.SEQ (stm, seq stms)

  fun unEx (Ex e) = e
    | unEx (Nx (T.EXP e)) = e
    | unEx (Nx s) = T.ESEQ (s, T.CONST 888)
    | unEx (Cx genstm) =
        let val r = Temp.newTemp ()
            val t = Temp.newLabel ()
            val f = Temp.newLabel ()
        in
          T.ESEQ (seq [T.MOVE (T.TEMP r, T.CONST 1),
                       genstm (t, f),
                       T.LABEL f,
                       T.MOVE (T.TEMP r, T.CONST 0),
                       T.LABEL t],
                  T.TEMP r)
        end

  fun unNx (Ex e) = T.EXP e
    | unNx (Nx n) = n
    | unNx cx = unNx (Ex (unEx cx))

  fun unCx (Ex (T.CONST 0)) = (fn (l1, l2) => T.JUMP (T.NAME l2, [l2]))
    | unCx (Ex (T.CONST 1)) = (fn (l1, l2) => T.JUMP (T.NAME l1, [l1]))
    | unCx (Ex e) = (fn (l1, l2) =>
                        let
                          val r = Temp.newTemp ()
                        in
                          seq [T.MOVE (T.TEMP r, e),
                               T.CJUMP (T.EQ, T.CONST 1, T.TEMP r, l1, l2)]
                        end)
    | unCx (Nx n) = ErrorMsg.impossible "Tried to unCx an Nx"
    | unCx (Cx c) = c

  fun levelEqual (Nested {parent=_, frame=_, id=id1},
                  Nested {parent=_, frame=_, id=id2}) = id1 = id2
    | levelEqual (Top, Top) = true
    | levelEqual _ = false

  fun getFPExp (target, current as (Nested {parent, frame, id}), fpExp) =
      if levelEqual (target, current) then
        fpExp
      else
        let val linkAccess :: _ = Frame.formals frame in
          getFPExp (target, parent, (Frame.exp linkAccess fpExp))
        end
      | getFPExp (target, Top, _) = ErrorMsg.impossible "Cannot have access from TOP level"

  fun simpleVar ((target, faccess), current) =
      Ex (Frame.exp faccess (getFPExp (target, current, T.TEMP Frame.FP)))

  (* TODO: Null checks *)
  fun fieldVar (varExp, offset) =
      Ex (T.MEM (T.BINOP (T.PLUS, unEx varExp, T.CONST (offset * Frame.wordSize))))

  (* TODO: add bounds checks *)
  fun subscriptVar (varExp, exps, dim) =
      let
        fun genIdxCode (idxExp, (sizeExp, offsetExp, sizeAddrExp, code)) =
          let
            val sizeTmp = T.TEMP (Temp.newTemp ())
            val offsetTmp = T.TEMP (Temp.newTemp ())
            val sizeAddrTmp = T.TEMP (Temp.newTemp ())
            val newSizeAddrExp = T.MOVE (sizeAddrTmp,
                                         T.BINOP (T.MINUS,
                                                  sizeAddrExp,
                                                  T.CONST Frame.wordSize))
            val newSizeExp = T.MOVE (sizeTmp,
                                     T.BINOP (T.MUL,
                                              sizeExp,
                                              T.MEM sizeAddrTmp))
            val newOffsetExp = T.MOVE (offsetTmp,
                                       T.BINOP (T.PLUS,
                                                offsetExp,
                                                T.BINOP (T.MUL,
                                                         unEx idxExp,
                                                         sizeExp)))
          in
            (sizeTmp,
             offsetTmp,
             sizeAddrTmp,
             code @ [newSizeAddrExp, newSizeExp, newOffsetExp])
          end
        val startAddrTmp = T.TEMP (Temp.newTemp ())
        val startSizeAddrExp = T.BINOP (T.PLUS,
                                        unEx varExp,
                                        T.CONST (dim * Frame.wordSize))
        val (_, offsetExp, _, code) = foldr genIdxCode
                                            (T.CONST 1, T.CONST 0, startAddrTmp, [])
                                            exps
        val code = seq code
      in
        Ex (T.ESEQ (T.MOVE (startAddrTmp, startSizeAddrExp),
                    T.MEM (T.BINOP (T.PLUS,
                                    startAddrTmp,
                                    T.ESEQ (code, T.BINOP (T.MUL,
                                                           T.CONST Frame.wordSize,
                                                           offsetExp))))))
      end

  fun assign (lExp, rExp) = Nx (T.MOVE (unEx lExp, unEx rExp))

  fun sequence [] = Ex (T.CONST 999)
    | sequence [exp] = exp
    | sequence (exp :: exps) =
        Ex (T.ESEQ (unNx exp, unEx (sequence exps)))

  fun whileExp (testExp, bodyExp, breakLabel) =
      let
        val testLabel = Temp.newLabel ()
        val bodyLabel = Temp.newLabel ()
        val test = unCx testExp
        val body = unNx bodyExp
      in
        Nx (seq [T.LABEL testLabel,
                 test (bodyLabel, breakLabel),
                 T.LABEL bodyLabel,
                 body,
                 T.JUMP (T.NAME testLabel, [testLabel]),
                 T.LABEL breakLabel])
      end

  fun forExp (varExp, initExp, limitExp, bodyExp, breakLabel) =
      let
        val var = unEx varExp
        val init = unEx initExp
        val limit = unEx limitExp
        val body = unNx bodyExp
        val bodyLabel = Temp.newLabel ()
        val incrLabel = Temp.newLabel ()
      in
        Nx (seq [T.MOVE (var, init),
                 T.CJUMP (T.LE, var, limit, bodyLabel, breakLabel),
                 T.LABEL bodyLabel,
                 body,
                 T.CJUMP (T.LT, var, limit, incrLabel, breakLabel),
                 T.LABEL incrLabel,
                 T.MOVE (var, T.BINOP (T.PLUS, var, T.CONST 1)),
                 T.JUMP (T.NAME bodyLabel, [bodyLabel]),
                 T.LABEL breakLabel])
      end

  val newBreakpoint = Temp.newLabel

  fun break (breakLabel) = Nx (T.JUMP (T.NAME breakLabel, [breakLabel]))

  fun negate exp =
      Cx (fn (t, f) =>
           T.CJUMP (T.EQ, T.CONST 0, exp, t, f))

  datatype oper = RELOP of T.relop
                | BINOP of T.binop

  fun trStrOp A.EqOp lExp rExp =
      Ex (Frame.externalCall ("stringEqual", [lExp, rExp]))
    | trStrOp A.NeqOp lExp rExp =
      negate (unEx (trStrOp A.EqOp lExp rExp))
    | trStrOp A.LtOp lExp rExp =
      Ex (Frame.externalCall ("stringLessThan", [lExp, rExp]))
    | trStrOp A.GtOp lExp rExp =
      negate (unEx (trStrOp A.LeOp lExp rExp))
    | trStrOp A.LeOp lExp rExp =
      Ex (Frame.externalCall ("stringLessThanOrEqual", [lExp, rExp]))
    | trStrOp A.GeOp lExp rExp =
      negate (unEx (trStrOp A.LtOp lExp rExp))
    | trStrOp _ _ _ = ErrorMsg.impossible "Attempting non-comparison on strings"

  fun trIntOp A.PlusOp = BINOP T.PLUS
    | trIntOp A.MinusOp = BINOP T.MINUS
    | trIntOp A.TimesOp = BINOP T.MUL
    | trIntOp A.DivideOp = BINOP T.DIV
    | trIntOp A.EqOp = RELOP T.EQ
    | trIntOp A.NeqOp = RELOP T.NE
    | trIntOp A.LtOp = RELOP T.LT
    | trIntOp A.LeOp = RELOP T.LE
    | trIntOp A.GtOp = RELOP T.GT
    | trIntOp A.GeOp = RELOP T.GE

  fun trPtrOp A.EqOp = T.EQ
    | trPtrOp A.NeqOp = T.NE
    | trPtrOp _ = ErrorMsg.impossible "Attempting non-equality test on pointers"

  fun binop (ty, leftExp, oper, rightExp) =
      let
        val leftExp = unEx leftExp
        val rightExp = unEx rightExp
      in
        case ty of
            Types.STRING => trStrOp oper leftExp rightExp
          | Types.INT =>
            (case trIntOp oper of
              BINOP b => Ex (T.BINOP (b, leftExp, rightExp))
            | RELOP p => Cx (fn (t, f) => T.CJUMP (p, leftExp, rightExp, t, f)))
          | _ => Cx (fn (t, f) => T.CJUMP (trPtrOp oper, leftExp, rightExp, t, f))
      end

  (* TODO: Special Cases *)
  fun ifExp (testExp, thenExp, elseExp) =
      let
        val r = Temp.newTemp ()
        val thenLabel = Temp.newLabel ()
        val elseLabel = Temp.newLabel ()
        val joinLabel = Temp.newLabel ()
      in
        case thenExp of
             Ex _ =>
               Ex (T.ESEQ (seq [(unCx testExp) (thenLabel, elseLabel),
                                T.LABEL thenLabel,
                                T.MOVE (T.TEMP r, unEx thenExp),
                                T.JUMP (T.NAME joinLabel, [joinLabel]),
                                T.LABEL elseLabel,
                                T.MOVE (T.TEMP r, unEx elseExp),
                                T.LABEL joinLabel],
                           T.TEMP r))
           | Nx _ =>
               Nx (seq [(unCx testExp) (thenLabel, elseLabel),
                        T.LABEL thenLabel,
                        unNx thenExp,
                        T.JUMP (T.NAME joinLabel, [joinLabel]),
                        T.LABEL elseLabel,
                        unNx elseExp,
                        T.LABEL joinLabel])
           | Cx _ =>
               Cx (fn labels =>
                    seq [(unCx testExp) (thenLabel, elseLabel),
                         T.LABEL thenLabel,
                         (unCx thenExp) labels,
                         T.LABEL elseLabel,
                         (unCx elseExp) labels])
      end

  fun callExp (label, args, current, Nested {parent=target as Nested _, frame, id}) =
      Ex (T.CALL (T.NAME label, getFPExp (target, current, T.TEMP Frame.FP) :: (map unEx args)))
    | callExp (label, args, current, Nested {parent=Top, frame, id}) =
      Ex (Frame.externalCall (Symbol.name label, map unEx args))
    | callExp (_, _, _, Top) = ErrorMsg.impossible "Function requires static link to top"

  fun recordExp exps =
      let
        val numFields = length exps
        val r = T.TEMP (Temp.newTemp ())
        val alloc = T.MOVE (r, Frame.externalCall ("malloc", [T.CONST (Frame.wordSize * numFields)]))
        val (fieldInits, _) = foldl (fn (exp, (inits, i)) =>
                                 (T.SEQ (inits,
                                         T.MOVE (unEx (fieldVar (Ex r, i)), unEx exp)),
                                  i + 1))
                               (alloc, 0)
                               exps
      in
        Ex (T.ESEQ (fieldInits, r))
      end

  fun arrayExp (dimExps, initExp) =
      let
        val dims = map unEx dimExps
        val dimTemps = map (fn _ => T.TEMP (Temp.newTemp ())) dims
        val productRegistersStm = seq (ListPair.mapEq
                                        (fn (exp, temp) => T.MOVE (temp, exp))
                                        (dims, dimTemps))
        val sizeExp = foldl (fn (exp, sizeExp) => T.BINOP (T.MUL, exp, sizeExp))
                            (hd dimTemps)
                            (tl dimTemps)
        val resultTemp = T.TEMP (Temp.newTemp ())
        fun ihatedrew (temp, i) =
            T.MOVE (T.MEM (T.BINOP (T.PLUS, resultTemp, T.CONST (Frame.wordSize * i))), temp)
        val (loadSizesStm, _) = foldl (fn (temp, (stm, i)) =>
                                        (T.SEQ (stm, ihatedrew (temp, i)), i + 1))
                                      (ihatedrew (hd dimTemps, 0), 1)
                                      (tl dimTemps)
      in
        Ex (T.ESEQ (seq [productRegistersStm,
                         T.MOVE (resultTemp,
                                 Frame.externalCall ("initArray",
                                                     [unEx initExp, sizeExp, T.CONST (length dims)])),
                         loadSizesStm],
                    resultTemp))
      end

  fun intLit n = Ex (T.CONST n)

  fun stringLit lit =
      let val lab = Temp.newLabel () in
        frags := Frame.STRING (lab, lit) :: (!frags);
        Ex (T.NAME lab)
      end

  fun procEntryExit {level=Nested {parent, frame, id}, body} =
      let
        val body = Frame.procEntryExit1 (frame, T.MOVE (T.TEMP Frame.RV, unEx body))
      in
        frags := Frame.PROC {body=body, frame=frame} :: (!frags)
      end
      | procEntryExit _ = ErrorMsg.impossible "Attempting to create procEntryExit for Top level"

  fun result () = !frags

  fun reset () = frags := []
end
