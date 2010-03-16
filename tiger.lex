type pos = int
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentDepth = ref 0
val commentStartPos = ref 0

val error = ErrorMsg.error

(* Create a lookup table for keywords *)

structure KeywordMap = BinaryMapFn (struct
  type ord_key = string
  val compare = String.compare
end)

val keywords = foldr KeywordMap.insert' KeywordMap.empty [
    ("array", Tokens.ARRAY),
    ("break", Tokens.BREAK),
    ("do", Tokens.DO),
    ("else", Tokens.ELSE),
    ("end", Tokens.END),
    ("for", Tokens.FOR),
    ("function", Tokens.FUNCTION),
    ("if", Tokens.IF),
    ("in", Tokens.IN),
    ("let", Tokens.LET),
    ("nil", Tokens.NIL),
    ("of", Tokens.OF),
    ("then", Tokens.THEN),
    ("to", Tokens.TO),
    ("type", Tokens.TYPE),
    ("var", Tokens.VAR),
    ("while", Tokens.WHILE)
]

fun tokenizeId (text, startPos, endPos) =
    case KeywordMap.find (keywords, text) of
      NONE => Tokens.ID (text, startPos, endPos)
    | SOME toKeyword => toKeyword (startPos, endPos)

(* Define a structure to encapsulate string-building logic *)

structure StringTokenBuilder =
struct
    val current = ref ""
    val startPos = ref 0
    val inString = ref false

    fun new pos =
        (current := "";
         startPos := pos;
         inString := true)

    fun append text =
        current := !current ^ text

    fun appendEscape (text, pos) =
        case Char.fromString text of
          SOME char => if Char.ord char < 128 then
                         append (String.str char)
                       else
                         error pos ("Illegal ASCII escape (must be less than " ^
                                    "128): " ^ text)
        | NONE => error pos ("Illegal escape sequence: " ^ text)

    fun build endPos =
        (inString := false;
         Tokens.STRING (!current, !startPos, endPos))

    fun incomplete () = !inString

    fun getStart () = !startPos

    fun reset () =
        (inString := false;
         startPos := 0;
         current := "")
end

fun recordNewline (pos) =
    (lineNum := !lineNum + 1;
     linePos := pos :: !linePos)

fun eof () =
    let val pos = hd (!linePos) in
      if StringTokenBuilder.incomplete () then
        error (StringTokenBuilder.getStart ()) "Unclosed string"
      else if !commentDepth > 0 then
        error (!commentStartPos) "Unclosed comment"
      else
        ();
      (StringTokenBuilder.reset ();
       commentDepth := 0;
       commentStartPos := 0;
       ErrorMsg.reset ());
      Tokens.EOF(pos,pos)
    end

%%

%s COMMENT STRING FEED;

asciiprintable = [\032\033\035-\091\093-\126];

%%

<INITIAL,COMMENT,FEED>\n => (recordNewline yypos;
                             continue ());

<INITIAL,FEED>[\t\r\f ]+ => (continue ());

<INITIAL>[a-zA-Z][a-zA-Z0-9_]* => (* Match identifiers *)
  (tokenizeId (yytext, yypos, yypos + size yytext));

<INITIAL>[0-9]+ => (* Match integers *)
  (Tokens.INT (valOf(Int.fromString yytext), yypos, yypos + size yytext));

<INITIAL>\" => (YYBEGIN STRING;
                StringTokenBuilder.new yypos;
                continue ());

<STRING>\" => (YYBEGIN INITIAL;
               StringTokenBuilder.build (yypos + 1));

<STRING>{asciiprintable}* =>
  (* Match and append printable ascii characters, /except newlines/ *)
  (StringTokenBuilder.append yytext;
   continue ());

<STRING>\\([nt\"\\]|[0-9]{3}|\^[@-_?]) =>
  (* Match all legal escape sequences except feed characters (range checking for
     ascii sequences is delegated) *)
  (StringTokenBuilder.appendEscape (yytext, yypos);
   continue ());

<STRING>\\(\^.|[^\t\r\f\n ]) =>
  (* This catches any control character (\^c) or non-feed escape character that
     wasn't already matched and reports an error *)
  (error yypos ("Illegal escape character: " ^ yytext);
   continue ());

<STRING>\\ =>
  (* Begin matching a feed sequence - the previous rule guarantees that the next
     character is one of the legal feed chars: \t \r \f \n or space *)
  (YYBEGIN FEED;
   continue ());

<STRING>\n => (error yypos "Illegal multiline string";
               recordNewline yypos;
               continue ());

<STRING>. => (error yypos ("Illegal string character: " ^ yytext);
              continue ());

<FEED>\\ => (YYBEGIN STRING;
             continue ());

<FEED>. => (YYBEGIN FEED;
            error yypos ("Illegal feed character (expected whitespace): " ^
                         yytext);
            continue ());

<INITIAL>"," => (Tokens.COMMA (yypos, yypos + 1));
<INITIAL>":" => (Tokens.COLON (yypos, yypos + 1));
<INITIAL>";" => (Tokens.SEMICOLON (yypos, yypos + 1));
<INITIAL>"(" => (Tokens.LPAREN (yypos, yypos + 1));
<INITIAL>")" => (Tokens.RPAREN (yypos, yypos + 1));
<INITIAL>"[" => (Tokens.LBRACK (yypos, yypos + 1));
<INITIAL>"]" => (Tokens.RBRACK (yypos, yypos + 1));
<INITIAL>"{" => (Tokens.LBRACE (yypos, yypos + 1));
<INITIAL>"}" => (Tokens.RBRACE (yypos, yypos + 1));
<INITIAL>"." => (Tokens.DOT (yypos, yypos + 1));
<INITIAL>"+" => (Tokens.PLUS (yypos, yypos + 1));
<INITIAL>"-" => (Tokens.MINUS (yypos, yypos + 1));
<INITIAL>"*" => (Tokens.TIMES (yypos, yypos + 1));
<INITIAL>"/" => (Tokens.DIVIDE (yypos, yypos + 1));
<INITIAL>"=" => (Tokens.EQ (yypos, yypos + 1));
<INITIAL>"<" => (Tokens.LT (yypos, yypos + 1));
<INITIAL>">" => (Tokens.GT (yypos, yypos + 1));
<INITIAL>"&" => (Tokens.AND (yypos, yypos + 1));
<INITIAL>"|" => (Tokens.OR (yypos, yypos + 1));
<INITIAL>"<>" => (Tokens.NEQ (yypos, yypos + 2));
<INITIAL>"<=" => (Tokens.LE (yypos, yypos + 2));
<INITIAL>">=" => (Tokens.GT (yypos, yypos + 2));
<INITIAL>":=" => (Tokens.ASSIGN (yypos, yypos + 2));

<INITIAL,COMMENT>"/*" => (YYBEGIN COMMENT;
                          commentDepth := (!commentDepth + 1);
                          commentStartPos := yypos;
                          continue ());

<COMMENT>"*/" => (commentDepth := (!commentDepth - 1);
                  if !commentDepth = 0 then YYBEGIN INITIAL else ();
                  continue ());

<COMMENT>. => (continue ());

<INITIAL>. => (error yypos ("Illegal character: " ^ yytext);
               continue ());
