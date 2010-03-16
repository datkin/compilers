signature ERRORMSG =
sig
    val anyErrors : bool ref
    val fileName : string ref
    val lineNum : int ref
    val linePos : int list ref
    val sourceStream : TextIO.instream ref
    val error : int -> string -> unit
    exception Error
    val impossible : string -> 'a   (* raises Error *)
    val reset : unit -> unit
end

structure Error =
struct
  type pos = int and symbol = Symbol.symbol
  datatype static = Lex of {pos: pos, msg: string}
                  | Parse of {pos: pos, msg: string}
end

structure ErrorMsg (* : ERRORMSG *) =
struct

  val anyErrors = ref false
  val lineNum = ref 1
  val linePos = ref [1]
  val errorLog : Error.static list ref = ref []
  val sourceName = ref "stdIn"

  fun reset name =
    (anyErrors := false;
     lineNum := 1;
     linePos := [1];
     errorLog = ref [];
     sourceName := name)

  exception Error

  fun posToStr pos =
    let fun look(a::rest,n) =
              if a<pos then
                String.concat [Int.toString n,
                               ".",
                               Int.toString (pos-a)]
              else look(rest,n-1)
          | look _ = "0.0"
    in
      look (!linePos, !lineNum)
    end

  fun error pos (msg : string) =
    print (!sourceName ^ ":" ^ posToStr pos ^ " Error: " ^ msg ^ "\n")

  fun impossible msg =
    (app print ["Error: Compiler bug: ",msg,"\n"];
     TextIO.flushOut TextIO.stdOut;
     raise Error)

  fun display Lex {pos, msg} = "lex error at " ^ posToStr pos ^ ": " ^ msg

  fun log err =
    (errorLog := err :: !errorLog;
     anyErrors := true;
     display err)

end
