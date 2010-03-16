signature ENV =
sig
  type ty = Types.ty (* Is this supposed to be bound? *)

  datatype enventry = VarEntry of {ty: ty}
                    | FunEntry of {formals: ty list, result: ty}

  val base_tenv : ty Symbol.table
  val base_venv : enventry Symbol.table
end

structure Env :> ENV =
struct
type ty = Types.ty

datatype enventry = VarEntry of {ty: ty}
                  | FunEntry of {formals: ty list, result: ty}

fun s (str) = Symbol.symbol str;

val base_tenv = foldr Symbol.enter' Symbol.empty [
  (s "string", Types.STRING),
  (s "int", Types.INT)
];

val base_venv = foldr Symbol.enter' Symbol.empty [
  (s "print", FunEntry {formals=[Types.STRING], result=Types.UNIT}),
  (s "flush", FunEntry {formals=[], result=Types.UNIT}),
  (s "getchar", FunEntry {formals=[], result=Types.STRING}),
  (s "ord", FunEntry {formals=[Types.STRING], result=Types.INT}),
  (s "chr", FunEntry {formals=[Types.INT], result=Types.STRING}),
  (s "size", FunEntry {formals=[Types.STRING], result=Types.INT}),
  (s "substring", FunEntry {formals=[Types.STRING, Types.INT, Types.INT], result=Types.STRING}),
  (s "concat", FunEntry {formals=[Types.STRING, Types.STRING], result=Types.STRING}),
  (s "not", FunEntry {formals=[Types.INT], result=Types.INT}),
  (s "exit", FunEntry {formals=[Types.INT], result=Types.BOTTOM})
];

end
