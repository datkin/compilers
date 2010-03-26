structure Tiger =
struct

fun compile (name, source) =
    (ErrorMsg.reset name;
     Translate.reset ();
     let
       val ast = Parse.parse (name, source) (* TODO: short circuit compilation on parse errors *)
       val _ = FindEscape.findEscape ast
       val result = Semant.transProg ast
     in
       (app ErrorMsg.display (!ErrorMsg.errorLog);
        result)
     end)

fun compileFile filename = compile (filename, TextIO.openIn filename)

fun compileStr str = compile ("string", TextIO.openString str)
end
