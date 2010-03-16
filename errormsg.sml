structure Error =
struct
type pos = int and symbol = Symbol.symbol
datatype error = Lex of {pos: pos, msg: string}
               | Parse of {pos: pos, msg: string}
               | CyclicTypeDec of {pos: pos, syms: symbol list}
               | UnboundType of {pos: pos, sym: symbol}
               | UnresolvedType of {pos: pos, sym: symbol}
               | UnboundRecordType of {pos: pos, sym: symbol} (* specifically for when we expected a record *)
               | UndefinedVar of {pos: pos, sym: symbol}
               | UndefinedFunction of {pos: pos, sym: symbol}
               | NameBoundToVar of {pos: pos, sym: symbol} (* when using a var name for a function *)
               | NameBoundToFunction of {pos: pos, sym: symbol} (* when a fun name is used as an lvalue *)
               | NonArrayType of {pos: pos, sym: symbol, actual: Types.ty}
               | NonRecordType of {pos: pos, sym: symbol, actual: Types.ty} (* for when the type was bound to a non record *)
               | NonArrayAccess of {pos: pos, actual: Types.ty}
               | NonRecordAccess of {pos: pos, field: symbol, actual: Types.ty}
               | NoSuchField of {pos: pos, field: symbol, record: Types.ty}
               | MissingField of {pos: pos, field: symbol, expected: Types.ty}
               | NilInitialization of {pos: pos, name: symbol}
               | IllegalBreak of {pos: pos}
               | NonUnitIf of {pos: pos, actual: Types.ty}
               | NonUnitFor of {pos: pos, actual: Types.ty}
               | NonUnitWhile of {pos: pos, actual: Types.ty}
               | NonUnitProcedure of {pos: pos, name: symbol, body: Types.ty} (* special case of type mismatch? *)
               | NonIntSubscript of {pos: pos, actual: Types.ty}
               | ArgumentMismatch of {pos: pos, actual: Types.ty, expected: Types.ty}
               | ArityMismatch of {pos: pos, name: symbol, actual: int, expected: int}
               | ArrayInitMismatch of {pos: pos, actual: Types.ty, expected: Types.ty}
               | ArraySizeMismatch of {pos: pos, actual: Types.ty}
               | AssignmentMismatch of {pos: pos, actual: Types.ty, expected: Types.ty}
               | ConditionMismatch of {pos: pos, actual: Types.ty}
               | FieldMismatch of {pos: pos, field: symbol, actual: Types.ty, expected: Types.ty}
               | ForRangeMismatch of {pos: pos, which: string, actual: Types.ty} (* todo: sum type for which? *)
               | IfBranchMismatch of {pos: pos, then': Types.ty, else': Types.ty}
               | OperandMismatch of {pos: pos, oper: Absyn.oper, actual: Types.ty, expected: Types.ty}
                 (* When the declared type doesn't match the actual type. *)
               | TypeMismatch of {pos: pos, actual: Types.ty, expected: Types.ty}
               | TypeRedefined of {pos: pos, name: symbol}
               | FunRedefined of {pos: pos, name: symbol}
               | ArgumentRedefined of {pos: pos, name: symbol, argument: symbol}
               | DuplicateField of {pos: pos, field: symbol}
               | DimensionMismatch of {pos: pos, ty: Types.ty, actual: int, expected: int}
end

signature ERRORMSG =
sig
  val anyErrors : bool ref
  val lineNum : int ref
  val linePos : int list ref
  val sourceName : string ref
  exception Error
  val impossible : string -> 'a   (* raises Error *)
  val reset : string -> unit
  val log : Error.error -> unit
  val display : Error.error -> unit
  val errorLog : Error.error list ref
  val mkStr : int -> string -> string
end

structure ErrorMsg : ERRORMSG =
struct

type pos = int and symbol = Symbol.symbol

  val n = Symbol.name
  val anyErrors = ref false
  val lineNum = ref 1
  val linePos = ref [1]
  val errorLog : Error.error list ref = ref []
  val sourceName = ref "stdIn"

  fun reset name = (anyErrors := false;
                    lineNum := 1;
                    linePos := [1];
                    errorLog := [];
                    sourceName := name)

  exception Error

  (* fun append text =
      (source := String.concat [!source, text]) *)

  fun posToStr pos =
      let fun look(a::rest,n) =
              if a<pos then String.concat [Int.toString n,
                                           ".",
                                           Int.toString (pos-a)]
              else look(rest,n-1)
            | look _ = "0.0"
      in
        look (!linePos, !lineNum)
      end

  fun mkStr pos (msg : string) = (* converts a pos and a msg to an appropriately formatted error *)
      (!sourceName ^ ":" ^ posToStr pos ^ " Error: " ^ msg ^ "\n")

  fun impossible msg =
      (app print ["Error: Compiler bug: ",msg,"\n"];
       TextIO.flushOut TextIO.stdOut;
       raise Error)

  fun operToString (Absyn.PlusOp) = "+"
    | operToString (Absyn.MinusOp) = "-"
    | operToString (Absyn.TimesOp) = "*"
    | operToString (Absyn.DivideOp) = "/"
    | operToString (Absyn.EqOp) = "="
    | operToString (Absyn.NeqOp) = "<>"
    | operToString (Absyn.LtOp) = "<"
    | operToString (Absyn.LeOp) = "<="
    | operToString (Absyn.GtOp) = ">"
    | operToString (Absyn.GeOp) = ">="

  fun toString (Error.Lex {pos, msg}) =
      mkStr pos ("Lexing: " ^ msg)
    | toString (Error.Parse {pos, msg}) =
      mkStr pos ("Parsing: " ^ msg)
    | toString (Error.CyclicTypeDec {pos, syms}) =
      mkStr pos ("Cannot resolve cyclic type declarations: " ^ (String.concatWith ", " (map n syms)))
    | toString (Error.UnboundType {pos, sym}) =
      mkStr pos ("Unbound type: " ^ n sym)
    | toString (Error.UnresolvedType {pos, sym}) =
      mkStr pos ("Unable to resolve type reference to " ^ n sym)
    | toString (Error.UnboundRecordType {pos, sym}) =
      mkStr pos ("Unbound record type: " ^ n sym)
    | toString (Error.UndefinedVar {pos, sym}) =
      mkStr pos ("Undefined variable: " ^ n sym)
    | toString (Error.UndefinedFunction {pos, sym}) =
      mkStr pos ("Undefined function: " ^ n sym)
    | toString (Error.NameBoundToVar {pos, sym}) =
      mkStr pos ("Name bound to variable, but expected function: " ^ n sym)
    | toString (Error.NameBoundToFunction {pos, sym}) =
      mkStr pos ("Name bound to function, but expected variable: " ^ n sym)
    | toString (Error.NonArrayType {pos, sym, actual}) =
      mkStr pos (n sym ^ " refers to " ^ Types.toString actual ^ " and not to an array")
    | toString (Error.NonRecordType {pos, sym, actual}) =
      mkStr pos (n sym ^ " refers to " ^ Types.toString actual ^ " and not to a record")
    | toString (Error.NonArrayAccess {pos, actual}) =
      mkStr pos ("Attempting to index into " ^ Types.toString actual)
    | toString (Error.NonRecordAccess {pos, field, actual}) =
      mkStr pos ("Attempting to access field '" ^ n field ^ "' of " ^ Types.toString actual)
    | toString (Error.NoSuchField {pos, field, record}) =
      mkStr pos (Types.toString record ^ " does not have field '" ^ n field ^ "'")
    | toString (Error.MissingField {pos, field, expected}) =
      mkStr pos ("Missing field '" ^ n field ^ "' of type " ^ Types.toString expected)
    | toString (Error.NilInitialization {pos, name}) =
      mkStr pos ("Initializing variable " ^ n name ^ " to nil")
    | toString (Error.IllegalBreak {pos}) =
      mkStr pos ("Break used outside of a loop")
    | toString (Error.NonUnitIf {pos, actual}) =
      mkStr pos ("If-then statements must have unit type, found " ^ Types.toString actual)
    | toString (Error.NonUnitFor {pos, actual}) =
      mkStr pos ("For statements must have unit type, found " ^ Types.toString actual)
    | toString (Error.NonUnitWhile {pos, actual}) =
      mkStr pos ("While statements must have unit type")
    | toString (Error.NonUnitProcedure {pos, name, body}) =
      mkStr pos ("Procedures must return unit (no type is specified but has return type): " ^ n name)
    | toString (Error.NonIntSubscript {pos, actual}) =
      mkStr pos ("Arrays must be indexed by integers, attempted to index with " ^ Types.toString actual)
    | toString (Error.ArgumentMismatch {pos, actual, expected}) =
      mkStr pos ("Argument type and expected type do not agree")
    | toString (Error.ArityMismatch {pos, name, actual, expected}) =
      mkStr pos ("Wrong arity, " ^ n name ^ " expects " ^ Int.toString actual ^ ", got " ^ Int.toString expected)
    | toString (Error.ArrayInitMismatch {pos, actual, expected}) =
      mkStr pos ("Array init value does not match array type")
    | toString (Error.ArraySizeMismatch {pos, actual}) =
      mkStr pos ("Array size must be an int")
    | toString (Error.AssignmentMismatch {pos, actual, expected}) =
      mkStr pos ("Trying to assign " ^ Types.toString actual ^ " to " ^ Types.toString expected)
    | toString (Error.ConditionMismatch {pos, actual}) =
      mkStr pos ("Conditions must be of type int")
    | toString (Error.FieldMismatch {pos, field, actual, expected}) =
      mkStr pos ("Wrong type for field " ^ n field ^ ", expected " ^ Types.toString expected ^ ", got " ^ Types.toString actual)
    | toString (Error.ForRangeMismatch {pos, which, actual}) =
      mkStr pos ("For-loop " ^ which ^ "-bound must be int")
    | toString (Error.IfBranchMismatch {pos, then', else'}) =
      mkStr pos ("If-then-else branches don't match")
    | toString (Error.OperandMismatch {pos, oper, actual, expected}) =
      mkStr pos (operToString oper ^ " expected " ^ Types.toString expected ^ " but operand was " ^ Types.toString actual) (* todo: pp types AND oper *)
    | toString (Error.TypeMismatch {pos, actual, expected}) =
      mkStr pos ("Declared type and actual type don't agree") (* todo: pp types *)
    | toString (Error.TypeRedefined {pos, name}) =
      mkStr pos ("Type name bound more than once in this declaration: " ^ n name)
    | toString (Error.FunRedefined {pos, name}) =
      mkStr pos ("Function name bound more than once in this declaration: " ^ n name)
    | toString (Error.ArgumentRedefined {pos, name, argument}) =
      mkStr pos ("Argument " ^ n argument ^ " redefined in " ^ n name)
    | toString (Error.DuplicateField {pos, field}) =
      mkStr pos ("Field " ^ n field ^ " defined multiple times")
    | toString (Error.DimensionMismatch {pos, ty, actual, expected}) =
      mkStr pos ("Provided " ^ Int.toString actual ^ " indices to " ^ Int.toString expected ^ "-dimensional " ^ Types.toString ty)

  fun display err = print (toString err)

  fun log err =
      (if not (List.exists (fn err' => err = err') (!errorLog)) then
         errorLog := err :: !errorLog (* avoid dupe error reporting - is there a better way? *)
       else
         ();
       anyErrors := true)

end
