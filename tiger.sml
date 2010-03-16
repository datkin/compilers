structure Tiger =
struct

fun compile (name, source) =
    (ErrorMsg.reset name;
     let val result = Semant.transProg (Parse.parse (name, source)) in
       (app ErrorMsg.display (!ErrorMsg.errorLog);
        result)
     end)

fun compileFile filename = compile (filename, TextIO.openIn filename)

fun compileStr str = compile ("string", TextIO.openString str)
end
