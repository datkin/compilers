structure Semant : sig
  val transProg : Absyn.exp -> {exp: Translate.exp, ty: Types.ty}
end =
struct

(* Useful abbreviations. *)
structure A = Absyn and E = Error and T = Types and Tr = Translate
val error = ErrorMsg.log
val n = Symbol.name

type pos = int and symbol = Symbol.symbol
type venv = Env.enventry Symbol.table
type expty = {exp: Translate.exp, ty: Types.ty}

(* Non-well-typed expressions are TOP. When a non-well-typed expression
   is encountered, it can be assumed an error has already been reported
   and the type checker should avoid emitting further errors related to
   that type. *)

fun absent (id : Symbol.symbol, list) =
    not (List.exists (fn id' => id = id') list)

(* This only looks up names in the environment (ie, it should not create new T.NAMEs for unbound ids?) *)
fun resolveTyName (tenv, name, pos) =
    case Symbol.look (tenv, name) of
      NONE => (error (E.UnboundType {pos=pos, sym=name});
               T.TOP)
    | SOME ty => ty

(* Take a list of symbols that have been newly introduced in the environment and
   resolve any name pointers. *)
fun resolveTyDecs (new, tenv, pos) = (* Pos is the beginning of the declaration. *)
    let
      fun reportCyclicTypeDec (pos, path) =
          let
            (* Find all the symbols in path that are mapped to by new names in the dec. *)
            val syms = List.filter (fn name =>
                                       (case Symbol.look (tenv, name) of
                                          SOME ty => List.exists (fn ty' => ty = ty')
                                                                 path
                                        | _ => false))
                                   new
          in
            error (E.CyclicTypeDec {pos=pos, syms=syms})
          end
      (* Collect all the Type.NAMEs directly accessible from a given type. *)
      fun collectNameTys name =
          (case Symbol.look (tenv, name) of
             SOME (T.RECORD (fields, _)) =>
             List.filter (fn ty => case ty of
                                     T.NAME _ => true
                                   | _ => false)
                         (map (fn (_, ty) => ty) fields)
           | SOME (T.ARRAY (nameTy as T.NAME _, _, _)) => [nameTy]
           | SOME (nameTy as T.NAME _) => [nameTy]
           | _ => [])
      fun setTy ty (T.NAME (_, tyref)) = tyref := SOME ty
        | setTy ty1 ty2 = raise Fail ("Trying to resolve non-name type: " ^
                                      (T.toString ty2) ^ " to " ^ (T.toString ty1))
      fun getName (T.NAME (name, _)) = name
        | getName ty = raise Fail ("Trying to get name of " ^ (T.toString ty))
      (* Continuously follow Type.NAMEs through the type environment
       * looking for the non-reference type the NAMEs are intended to
       * point at. Once a "concrete" type has been found, all the
       * NAMEs are updated to point to it, using setTy. If a cycle is
       * found, all NAMEs are pointed to TOP. *)
      fun resolveFully (ty as T.NAME (name, tyref), path) =
          (case !tyref of
             NONE => if List.exists (fn ty' => ty = ty') path then
                       (reportCyclicTypeDec (pos, path);
                        resolveFully (T.TOP, ty :: path))
                     else
                       (case Symbol.look (tenv, name) of
                          NONE => (error (E.UnresolvedType {pos=pos, sym=name});
                                   resolveFully (T.TOP, ty :: path))
                        | SOME ty' => resolveFully (ty', ty :: path))
           | SOME ty' => resolveFully (ty', path))
        | resolveFully (ty, path) = map (setTy ty) path
    in
      map (fn ty => resolveFully (ty, []))
          (List.concat (map collectNameTys new))
    end

fun operTy (A.EqOp) = T.BOTTOM
  | operTy (A.NeqOp) = T.BOTTOM
  | operTy _ = T.INT

(* Absyn.ty -> Types.ty : Construct a type from an AST node *)
(* This is the only place where Types.tys should be created. *)
fun transTy (tenv, A.NameTy (name, _), _) =
    (case Symbol.look (tenv, name) of
       NONE => T.NAME (name, ref NONE)
     (* Use Types.NAME (name, ref (SOME ty))) instead? *)
     | SOME ty => ty)
  | transTy (tenv, A.RecordTy (fields), pos) =
    T.RECORD ((map (fn {name, escape=_, typ, pos=pos'} =>
                       (name, (transTy (tenv, A.NameTy (typ, pos'), pos))))
                   fields),
              pos)
  | transTy (tenv, A.ArrayTy (sym, dim, pos'), pos) =
    T.ARRAY (transTy (tenv, A.NameTy (sym, pos'), pos), dim, pos)

(* (symbol * exp * pos) list * symbol -> exp *)
(* Lookup the entry corresponding to the given field
 * from an Absyn.RecordExp. *)
fun findFieldEntries (fields, field : Symbol.symbol) =
    List.filter (fn (field', _, _) => field = field') fields

fun errorIf condition err = if condition then error err else ()

fun expect actual expected err =
    errorIf (T.wellTyped actual andalso T.wellTyped expected andalso
             not (T.subtype actual expected))
            err

(* All adjacent function definitions have been added to
 * the variable environment before this is called, so legal
 * recursive calls will type check just fine. *)
and transFunDec (venv, tenv, {name, params, result, body, pos}) =
    let
      fun bind ({name, escape=_, typ, pos}, access) =
          (name, Env.VarEntry {access=access, ty=resolveTyName (tenv, typ, pos)})
      val level = case Symbol.look (venv, name) of
                    SOME (Env.FunEntry e) => #level e
                  | _ => (ErrorMsg.impossible ("Couldn't find function " ^ n name);
                          raise Fail ("Couldn't find function " ^ n name))
      val venv' = foldr Symbol.enter' venv (ListPair.mapEq bind
                                                           (params,
                                                            (Translate.formals level)))
      val {exp=_, ty=actual} = transExp (venv', tenv, level, NONE, body)
    in
      case result of
        NONE => expect actual T.UNIT
                       (E.NonUnitProcedure {pos=pos, name=name, body=actual})
      | SOME (typ, pos) => let val expected = resolveTyName (tenv, typ, pos) in
                             expect actual expected
                                    (E.TypeMismatch {pos=pos, actual=actual, expected=expected})
                           end;
      {exp=Tr.BOGUS, ty=Types.UNIT}
    end

and transDec (venv, tenv, level, _, A.FunctionDec fundecs) = (* functions *)
    let
      (* Process a function argument specification, adding the type
       * of the argument and its name to an accumulator. The types
       * are used after all args are processed to create an Env.FunEntry
       * and the arugment names are passed along to check uniqueness of
       * subsequent argument names.
       * The function name is curried out for use with fold. *)
      fun paramToFormal func ({name, escape, typ, pos}, (tys, names)) =
          (errorIf (List.exists (fn n' => name = n') names)
                   (E.ArgumentRedefined {pos=pos, name=func, argument=name});
           (tys @ [resolveTyName (tenv, typ, pos)], name :: names))
      fun resultToTy NONE = T.UNIT
        | resultToTy (SOME (typ, pos)) = resolveTyName (tenv, typ, pos)
      fun addFun (dec as {name, params, result, body, pos},
                  (seen, venv)) =
          if absent (name, seen) then
            let
              val label = Temp.newLabel ()
              val level' = Translate.newLevel {parent=level, name=label,
                                               formals=map (fn dec => !(#escape dec)) params}
              val entry = Env.FunEntry {label=label, level=level',
                                        formals=(#1 (foldl (paramToFormal name)
                                                           ([], [])
                                                           params)),
                                        result=resultToTy result}
            in
              (name :: seen, Symbol.enter (venv, name, entry))
            end
          else
            (error (Error.FunRedefined {pos=pos, name=name});
             (seen, venv))
      val (_, venv') = foldl addFun ([], venv) fundecs
    in
      map (fn fundec => transFunDec (venv', tenv, fundec)) fundecs;
      ({venv=venv', tenv=tenv}, [])
    end
  | transDec (venv, tenv, level, bp, A.VarDec {name, escape, typ, init, pos}) = (* var *)
    let
      val access = Translate.allocLocal level (!escape)
      val {exp=rExp, ty=actual} = transExp (venv, tenv, level, bp, init)
      val declared = case typ of
                       SOME (name, pos) => resolveTyName (tenv, name, pos)
                     | NONE => actual
    in
      errorIf (T.equalTy declared T.NIL) (E.NilInitialization {pos=pos, name=name});
      expect actual declared
             (E.AssignmentMismatch {pos=pos, actual=actual, expected=declared});
      ({venv=Symbol.enter (venv, name, Env.VarEntry {access=access, ty=declared}), tenv=tenv},
       [Tr.assign (Tr.simpleVar (access, level), rExp)])
    end
  | transDec (venv, tenv, _, _, A.TypeDec decs) = (* types *)
    let fun addType ({name, ty, pos}, (new, tenv)) =
            if absent (name, new) then
              (new @ [name], Symbol.enter (tenv, name, transTy (tenv, ty, pos)))
            else (* If the name was already bound by these decs, don't rebind it. *)
              (error (Error.TypeRedefined {pos=pos, name=name});
               (new, tenv))
      val (new, tenv') = foldl addType ([], tenv) decs
      val pos = case List.getItem decs of
                  NONE => 0
                | SOME ({name=_, ty=_, pos}, _) => pos
    in
      resolveTyDecs (new, tenv', pos);
      ({venv=venv, tenv=tenv'}, [])
    end

and transExp (venv, tenv, level, bp, exp) =
    let
      fun transExp' exp = transExp (venv, tenv, level, bp, exp)
      fun getTy exp = #ty (transExp (venv, tenv, level, bp, exp))

      and transIdxExp exp =
          let val {exp=idxExp, ty=actual} = transExp (venv, tenv, level, bp, exp) in
            expect actual T.INT
                   (E.NonIntSubscript {pos=A.getPosExp exp, actual=actual});
            idxExp
          end

      (* Determine the type of an lvalue. *)
      and transVar (A.SimpleVar (name, pos)) = (* var *)
          (case Symbol.look (venv, name) of
             SOME (Env.VarEntry {access, ty}) =>
                {exp=Tr.simpleVar (access, level), ty=ty}
           | SOME (Env.FunEntry _) => (error (E.NameBoundToFunction {pos=pos, sym=name});
                                       {exp=Tr.BOGUS, ty=T.TOP})
           | NONE => (error (E.UndefinedVar {pos=pos, sym=name});
                      {exp=Tr.BOGUS, ty=T.TOP}))
        | transVar (A.FieldVar (var, field, pos)) = (* record *)
          (case transVar var of
             {exp=varExp, ty=record as T.RECORD (fields, _)} =>
             let fun findAndCount (_,  result as (SOME ty, _)) = result
                   | findAndCount ((f', ty), (NONE, i)) = if f' = field then
                                                           (SOME ty, i)
                                                          else
                                                           (NONE, i + 1)
             in
               case foldl findAndCount (NONE, 0) fields of
                    (SOME ty, i) => {exp=Tr.fieldVar (varExp, i), ty=ty}
                  | (NONE, _) => (error (E.NoSuchField {pos=pos, field=field, record=record});
                                  {exp=Tr.BOGUS, ty=T.TOP})
             end
           | {exp=_, ty} => (error (E.NonRecordAccess {pos=pos, field=field, actual=ty});
                             {exp=Tr.BOGUS, ty=T.TOP}))
        | transVar (A.SubscriptVar (var, exps, pos)) = (* array *)
          let
            val indices = length exps
            val idxExps = map transIdxExp exps
          in
            case transVar var of
              {exp=varExp, ty=array_ty as T.ARRAY (ty, dim, _)} =>
              (errorIf (indices <> dim)
                       (E.DimensionMismatch {pos=pos, ty=array_ty, expected=dim, actual=indices});
               {exp=Tr.subscriptVar (varExp, idxExps, dim), ty=ty})
            | {exp=_, ty} => (errorIf (T.wellTyped ty)
                                      (E.NonArrayAccess {pos=pos, actual=ty});
                              {exp=Tr.BOGUS, ty=T.TOP})
          end

      and transCall {func=name, args=arg_exps, pos} =
          (case Symbol.look (venv, name) of
             NONE => (error (E.UndefinedFunction {pos=pos, sym=name});
                      {exp=Tr.BOGUS, ty=T.TOP})
           | SOME (Env.VarEntry _) => (error (E.NameBoundToVar {pos=pos, sym=name});
                                       {exp=Tr.BOGUS, ty=T.TOP})
           | SOME (Env.FunEntry {label, level, formals, result}) =>
             (* Verify the arg types against the declared types. *)
             (ListPair.appEq (fn (expected, exp) =>
                                 let val actual = getTy exp in
                                   expect actual expected
                                          (E.ArgumentMismatch {pos=(A.getPosExp exp), actual=actual, expected=expected})
                                 end)
                             (formals, arg_exps)
              handle ListPair.UnequalLengths =>
                     error (E.ArityMismatch {pos=pos, name=name, actual=length arg_exps, expected=length formals});
              {exp=Tr.BOGUS, ty=result}))

      and transOp {left, oper, right, pos} =
          let
            fun operTy (T.STRING, _) = T.STRING
              | operTy (T.INT, _) = T.INT
              | operTy (ty, A.NeqOp) = ty
              | operTy (ty, A.EqOp) = ty
              | operTy _ = T.INT
            val {exp=lExp, ty=left_ty} = transExp' left
            val {exp=rExp, ty=right_ty} = transExp' right
            val expected = operTy (left_ty, oper)
            val left_join = T.join (left_ty, expected)
            val actual = T.join (if T.wellTyped left_join then left_join else expected, right_ty)
          in
            if T.wellTyped left_ty andalso not (T.wellTyped left_join) then
              (error (E.OperandMismatch {pos=(A.getPosExp left), oper=oper, actual=left_ty, expected=expected});
               {exp=Tr.BOGUS, ty=T.INT})
            else if T.wellTyped left_join andalso T.wellTyped right_ty andalso not (T.wellTyped actual) then
              (error (E.OperandMismatch {pos=(A.getPosExp right), oper=oper, actual=right_ty, expected=left_join});
               {exp=Tr.BOGUS, ty=T.INT})
            else
              {exp=Tr.binop (actual, lExp, oper, rExp), ty=T.INT}
          end

      and transRecord {fields=field_exps, typ, pos} =
          (case Symbol.look (tenv, typ) of
             SOME (record as Types.RECORD (fields, _)) =>
             let fun trField (field, expected) =
                     case findFieldEntries (field_exps, field) of
                       [(_, exp, pos)] =>
                       let val {exp, ty=actual} = transExp' exp in
                         expect actual expected
                                (E.FieldMismatch {pos=pos, field=field, actual=actual, expected=expected});
                         exp
                       end
                     | _ :: _ => (error (E.DuplicateField {pos=pos, field=field});
                                  Tr.BOGUS)
                     | [] => (error (E.MissingField {pos=pos, field=field, expected=expected});
                              Tr.BOGUS)
               val fieldTrExps = map trField fields
             in
               {exp=Tr.recordExp fieldTrExps, ty=record}
             end
           | SOME actual => (error (E.NonRecordType {pos=pos, sym=typ, actual=actual});
                             {exp=Tr.BOGUS, ty=T.TOP})
           | NONE => (error (E.UnboundRecordType {pos=pos, sym=typ});
                      {exp=Tr.BOGUS, ty=T.TOP}))

      and transSeq exps =
          foldl (fn ((exp, _), {exp=trexp, ty=_}) =>
                  let
                    val {exp=newExp, ty} = transExp (venv, tenv, level, bp, exp)
                  in
                    {exp=Tr.sequence [trexp, newExp], ty=ty}
                  end)
                {exp=Tr.BOGUS, ty=T.UNIT}
                exps

      and transAssign {var, exp, pos} =
          let
            val {exp=lExp, ty=expected} = transVar var
            val {exp=rExp, ty=actual} = transExp (venv, tenv, level, bp, exp)
          in
            (expect actual expected
                    (E.AssignmentMismatch {pos=pos, actual=actual, expected=expected});
             {exp=Tr.assign (lExp, rExp), ty=T.UNIT})
          end

      and transIf {test, then', else', pos} =
          let
            val {exp=testExp, ty=test_ty} = transExp (venv, tenv, level, bp, test)
            val {exp=thenExp, ty=then_ty} = transExp (venv, tenv, level, bp, then')
            val {exp=elseExp, ty=else_ty} =
              case else' of
                   NONE => {exp=Tr.UNIT, ty=T.UNIT}
                 | SOME exp => transExp' exp
            val actual = case else' of
                           NONE => T.UNIT
                         | SOME _ => T.join (then_ty, else_ty)
          in
            expect test_ty T.INT
                   (E.ConditionMismatch {pos=(A.getPosExp test), actual=test_ty});
            case else' of
              NONE => expect then_ty T.UNIT
                             (E.NonUnitIf {pos=(A.getPosExp then'), actual=then_ty})
            | SOME exp => errorIf (T.wellTyped then_ty andalso T.wellTyped else_ty andalso
                                   not (T.wellTyped actual))
                                  (E.IfBranchMismatch {pos=(A.getPosExp exp), then'=then_ty, else'=else_ty});
            {exp=Tr.ifExp (testExp, thenExp, elseExp), ty=actual}
          end

      and transWhile {test, body, pos} =
          let
            val breakpoint = Tr.newBreakpoint ()
            val {exp=testExp, ty=test_ty} = transExp (venv, tenv, level, bp, test)
            val {exp=bodyExp, ty=body_ty} = transExp (venv, tenv, level, SOME breakpoint, body)
          in
            expect test_ty T.INT
                   (E.ConditionMismatch {pos=(A.getPosExp test), actual=test_ty});
            expect body_ty T.UNIT
                   (E.NonUnitWhile {pos=(A.getPosExp body), actual=body_ty});
            {exp=Tr.whileExp (testExp, bodyExp, breakpoint), ty=Types.UNIT}
          end

      and transFor {var, escape, lo, hi, body, pos} =
          let
            val access = Tr.allocLocal level (!escape)
            val breakpoint = Tr.newBreakpoint ()
            val {exp=loExp, ty=lo_ty} = transExp (venv, tenv, level, bp, lo)
            val {exp=hiExp, ty=hi_ty} = transExp (venv, tenv, level, bp, hi)
            val venv' = Symbol.enter (venv, var, Env.VarEntry {access=access, ty=Types.INT})
            val {exp=bodyExp, ty=body_ty} = transExp (venv', tenv, level, SOME breakpoint, body)
          in
            expect lo_ty Types.INT
                   (E.ForRangeMismatch {pos=(A.getPosExp lo), which="lower", actual=lo_ty});
            expect hi_ty Types.INT
                   (E.ForRangeMismatch {pos=(A.getPosExp hi), which="upper", actual=hi_ty});
            expect body_ty Types.UNIT
                   (E.NonUnitFor {pos=pos, actual=body_ty});
            {exp=Tr.forExp (Tr.simpleVar (access, level), loExp, hiExp, bodyExp, breakpoint), ty=T.UNIT}
          end

      and transLet {decs, body, pos} =
          let
            val ({venv=venv', tenv=tenv'}, decExps) =
              foldl (fn (dec, ({venv, tenv}, decExps)) =>
                      let
                        val (envs, decExps') = transDec (venv, tenv, level, bp, dec)
                      in
                        (envs, (decExps @ decExps'))
                      end)
                    ({venv=venv, tenv=tenv}, [])
                    decs
            val {exp=bodyExp, ty=ty} = transExp (venv', tenv', level, bp, body)
          in
            {exp=Tr.sequence (decExps @ [bodyExp]), ty=ty}
          end

      and transArray {typ, dims, init, pos} =
          let
            val indices = length dims
            val {exp=initExp, ty=init_ty} = transExp (venv, tenv, level, bp, init)
            fun transDim dim =
                let
                  val {exp=dimExp, ty=dimType} = transExp' dim
                in
                  (expect dimType T.INT
                    (E.ArraySizeMismatch {pos=A.getPosExp dim, actual=dimType});
                   dimExp)
                end
            val dimExps = map transDim dims
          in
            case resolveTyName (tenv, typ, pos) of
              array_ty as T.ARRAY (element_ty, dim, _) =>
              (errorIf (indices <> dim)
                       (E.DimensionMismatch{pos=pos, ty=array_ty, expected=dim, actual=indices});
               expect init_ty element_ty
                      (E.ArrayInitMismatch {pos=(A.getPosExp init),
                                            actual=init_ty,
                                            expected=element_ty});
               {exp=Tr.arrayExp (dimExps, initExp), ty=array_ty})
            | actual => (errorIf (T.wellTyped actual)
                                 (E.NonArrayType {pos=pos, sym=typ, actual=actual});
                         {exp=Tr.BOGUS, ty=T.TOP})
          end
    in
      case exp of
        A.NilExp _ => {exp=Tr.NIL, ty=T.NIL}
      | A.IntExp (n, _) => {exp=Tr.intLit n, ty=T.INT}
      | A.StringExp (lit, _) => {exp=Tr.stringLit lit, ty=T.STRING}
      | A.VarExp var => transVar var
      | A.CallExp call => transCall call
      | A.OpExp op' => transOp op'
      | A.RecordExp record => transRecord record
      | A.SeqExp (exps, _) => transSeq exps
      | A.AssignExp assign => transAssign assign
      | A.IfExp if' => transIf if'
      | A.WhileExp while' => transWhile while'
      | A.ForExp for => transFor for
      | A.LetExp let' => transLet let'
      | A.ArrayExp array => transArray array
      | A.BreakExp pos =>
          case bp of
               NONE => (error (E.IllegalBreak {pos=pos}); {exp=Tr.BOGUS, ty=T.BOTTOM})
             | SOME breakpoint => {exp=Tr.break breakpoint, ty=T.BOTTOM}
    end

fun transProg exp = transExp (Env.base_venv,
                              Env.base_tenv,
                              Translate.newLevel {name=Temp.newLabel (), parent=Translate.outermost, formals=[]},
                              NONE,
                              exp)

end
