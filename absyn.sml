structure Absyn =
struct

type pos = int   and   symbol = Symbol.symbol

(* NB: Appel uses "typ" to refer to the symbol representing a type identifier
       and "ty" to refer to *actual* types (either Absyn.ty or Types.ty).
       This is a rather annoying naming "scheme". *)
datatype var = SimpleVar of symbol * pos
             | FieldVar of var * symbol * pos
             | SubscriptVar of var * exp * pos

     and exp = VarExp of var
             | NilExp of pos
             | IntExp of int * pos
             | StringExp of string * pos
             | CallExp of {func: symbol, args: exp list, pos: pos}
             | OpExp of {left: exp, oper: oper, right: exp, pos: pos}
             | RecordExp of {fields: (symbol * exp * pos) list,
                             typ: symbol, pos: pos}
             | SeqExp of (exp * pos) list * pos
             | AssignExp of {var: var, exp: exp, pos: pos}
             | IfExp of {test: exp, then': exp, else': exp option, pos: pos}
             | WhileExp of {test: exp, body: exp, pos: pos}
             | ForExp of {var: symbol, escape: bool ref,
                          lo: exp, hi: exp, body: exp, pos: pos}
             | BreakExp of pos
             | LetExp of {decs: dec list, body: exp, pos: pos}
             | ArrayExp of {typ: symbol, size: exp, init: exp, pos: pos}

     and dec = FunctionDec of fundec list
             | VarDec of {name: symbol,
                          escape: bool ref,
                          typ: (symbol * pos) option,
                          init: exp,
                          pos: pos}
             | TypeDec of {name: symbol, ty: ty, pos: pos} list

     and ty = NameTy of symbol * pos
            | RecordTy of field list
            | ArrayTy of symbol * pos

     and oper = PlusOp | MinusOp | TimesOp | DivideOp
              | EqOp | NeqOp | LtOp | LeOp | GtOp | GeOp

withtype field = {name: symbol, escape: bool ref,
                  typ: symbol, pos: pos}
     and   fundec = {name: symbol,
                     params: field list,
                     result: (symbol * pos) option,
                     body: exp,
                     pos: pos}

fun getPosExp (VarExp var) =
    (case var of
      SimpleVar (_, pos) => pos
    | FieldVar (_, _, pos) => pos
    | SubscriptVar (_, _, pos) => pos)
  | getPosExp (NilExp pos) = pos
  | getPosExp (IntExp (_, pos)) = pos
  | getPosExp (StringExp (_, pos)) = pos
  | getPosExp (CallExp {func=_, args=_, pos}) = pos
  | getPosExp (OpExp {left=_, oper=_, right=_, pos}) = pos
  | getPosExp (RecordExp {fields=_, typ=_, pos}) = pos
  | getPosExp (SeqExp (_, pos)) = pos
  | getPosExp (AssignExp {var=_, exp=_, pos}) = pos
  | getPosExp (IfExp {test=_, then'=_, else'=_, pos}) = pos
  | getPosExp (WhileExp {test=_, body=_, pos}) = pos
  | getPosExp (ForExp {var=_, escape=_, lo=_, hi=_, body=_, pos}) = pos
  | getPosExp (BreakExp pos) = pos
  | getPosExp (LetExp {decs=_, body=_, pos}) = pos
  | getPosExp (ArrayExp {typ=_, size=_, init=_, pos}) = pos

end
