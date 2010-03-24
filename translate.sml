signature TRANSLATE =
sig
  type exp
  type level
  type access

  val BOGUS : exp

  val outermost : level
  val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access

  val simpleVar : (access * level) -> exp
  val fieldVar : (exp * int) -> exp
  val subscriptVar : (exp * exp list * int) -> exp

  val debug : exp -> unit
  val temp : unit -> exp
end

structure Translate :> TRANSLATE =
struct
  structure T = Tree
  datatype exp = Ex of T.exp
               | Nx of T.stm
               | Cx of Temp.label * Temp.label -> T.stm

  fun temp () = Ex (T.TEMP (Temp.newTemp ()))

  val BOGUS = Ex (T.CONST 0)
  val NOOP = T.EXP (T.CONST 0)

  datatype level = Top | Nested of {parent: level, frame: Frame.frame, id: unit ref}
  type access = level * Frame.access

  val outermost = Top

  fun newLevel {parent, name, formals} =
      Nested {parent=parent, frame=Frame.newFrame {name=name, formals=true :: formals}, id=ref ()}

  fun formals (level as (Nested {parent, frame, id})) =
      (case Frame.formals frame of
         [] => (ErrorMsg.impossible "Frame has no static link"; [])
       | _ :: formals => map (fn frameAccess => (level, frameAccess)) formals)
    | formals Top = []

  fun allocLocal (level as Nested {parent, frame, id}) escapes = (level, Frame.allocLocal frame escapes)
    | allocLocal Top _ = ErrorMsg.impossible "Attempted to allocate in the outermost frame."

  fun seq [] = T.EXP (T.CONST 0)
    | seq [stm1, stm2] = T.SEQ (stm1, stm2)
    | seq (stm :: stms) = T.SEQ (stm, seq stms)

  fun unEx (Ex e) = e
    | unEx (Nx s) = T.ESEQ (s, T.CONST 0)
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

  fun simpleVar ((targetLevel, faccess), curLevel) =
    let
      fun getFPExp (curLevel as (Nested {parent, frame, id}), fpExp) =
          if levelEqual (targetLevel, curLevel) then
            fpExp
          else
            let val linkAccess :: _ = Frame.formals frame in
              getFPExp (parent, (Frame.exp linkAccess fpExp))
            end
          | getFPExp _ = ErrorMsg.impossible "Cannot have access from TOP level"
    in
      Ex (Frame.exp faccess (getFPExp (curLevel, T.TEMP Frame.FP)))
    end

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
           T.SEQ (code, seq [newSizeAddrExp, newSizeExp, newOffsetExp]))
        end
      val startAddrTmp = T.TEMP (Temp.newTemp ())
      val startSizeAddrExp = T.BINOP (T.PLUS,
                                      unEx varExp,
                                      T.CONST (dim * Frame.wordSize))
      val (_, offsetExp, _, code) = foldr genIdxCode
                                          (T.CONST 1, T.CONST 0, startAddrTmp, NOOP)
                                          exps
    in
      Ex (T.ESEQ (T.MOVE (startAddrTmp, startSizeAddrExp),
                  T.MEM (T.BINOP (T.PLUS,
                                  startAddrTmp,
                                  T.ESEQ (code, T.BINOP (T.MUL,
                                                         T.CONST Frame.wordSize,
                                                         offsetExp))))))
    end

    (* TODO: REMOVE ME! *)
    fun debug exp = Printtree.printtree (TextIO.stdOut, unNx exp)
end
