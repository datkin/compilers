structure Parse : sig val parse : string * TextIO.instream -> Absyn.exp end =
struct
  structure TigerLrVals = TigerLrValsFun(structure Token = LrParser.Token)
  structure Lex = TigerLexFun(structure Tokens = TigerLrVals.Tokens)
  structure TigerP = Join(structure ParserData = TigerLrVals.ParserData
                          structure Lex=Lex
                          structure LrParser = LrParser)

  fun parse (name, source) =
      let fun get _ = TextIO.input source
        fun parseerror (s, p1, p2) = ErrorMsg.log (Error.Parse {pos=p1, msg=s})
        val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
        val (absyn, _) = TigerP.parse(30, lexer, parseerror, ())
      in TextIO.closeIn source;
         absyn
      end handle LrParser.ParseError => raise ErrorMsg.Error

end
