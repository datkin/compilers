signature ENV =
sig
  type ty = Types.ty (* Is this supposed to be bound? *)

  datatype enventry = VarEntry of {access: Translate.access,
                                   ty: ty}
                    | FunEntry of {label: Temp.label,
                                   level: Translate.level,
                                   formals: ty list,
                                   result: ty}

  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
end

structure Env :> ENV =
struct
type ty = Types.ty

datatype enventry = VarEntry of {access: Translate.access,
                                 ty: ty}
                  | FunEntry of {label: Temp.label,
                                 level: Translate.level,
                                 formals: ty list,
                                 result: ty}

fun s (str) = Symbol.symbol str;

val base_tenv = foldr Symbol.enter' Symbol.empty [
  (s "string", Types.STRING),
  (s "int", Types.INT)
];

fun newBuiltin (name, formals, result) =
    let
      val label = Temp.namedLabel name
      val level = Translate.newLevel {parent=Translate.outermost,
                                      name=label,
                                      formals=map (fn _ => false) formals}
    in
      (s name, FunEntry {label=label, level=level, formals=formals, result=result})
    end

val base_venv = foldr Symbol.enter' Symbol.empty [
  newBuiltin ("print", [Types.STRING], Types.UNIT),
  newBuiltin ("flush", [], Types.UNIT),
  newBuiltin ("getchar", [], Types.STRING),
  newBuiltin ("ord", [Types.STRING], Types.INT),
  newBuiltin ("chr", [Types.INT], Types.STRING),
  newBuiltin ("size", [Types.STRING], Types.INT),
  newBuiltin ("substring", [Types.STRING, Types.INT, Types.INT], Types.STRING),
  newBuiltin ("concat", [Types.STRING, Types.STRING], Types.STRING),
  newBuiltin ("not", [Types.INT], Types.INT),
  newBuiltin ("exit", [Types.INT], Types.BOTTOM)
];

end
