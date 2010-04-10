structure Tester =
struct

(* If any of these options is NONE it means that we don't have
 * an expected value for that part of the test and it should
 * just be ingored (ie the test should implicitly pass).
 * The following test is a no-op and should always pass:
 * {name="foo",
 *  source=Text.openString "...",
 *  parse=(NONE, NONE),
 *  check=(NONE, NONE)}
 *)
type test = {name: string,
             source: TextIO.instream,
             parse: (Absyn.exp option * Error.error list option),
             check: (Types.ty option * Error.error list option)}

fun checkErrors (NONE) = true
  | checkErrors (SOME (expected : Error.error list)) =
    let
      (* Go through the list expected errors and remove
       * them from the ErrorMsg log as they are found.
       * The test fails if any expected error message is
       * missing or if the ErrorMsg log is not empty after
       * removing all the expected errors. *)
      fun findExpected error =
          case List.find (fn error' => error = error')
                         (!ErrorMsg.errorLog) of
            NONE => (print "Expected error not found: ";
                     ErrorMsg.display error;
                     false)
          | SOME _ => (ErrorMsg.errorLog :=
                       List.filter (fn error' => error <> error')
                                   (!ErrorMsg.errorLog);
                       true)
      val allErrorsFound = List.all findExpected expected
      (* Print the remaining (unexpected) errors... *)
      val _ = app (fn (error) => ErrorMsg.display error)
                  (!ErrorMsg.errorLog)
      val unexpectedErrorCount = length (!ErrorMsg.errorLog)
    in
      (* Clear all the errors logged in this phase, so they aren't
       * reported again in the next phase. *)
      (ErrorMsg.errorLog := [];
       unexpectedErrorCount = 0 andalso allErrorsFound)
    end

fun checkAst (NONE, _) = true
  | checkAst (SOME expected, actual) =
    if actual = expected then
      true
    else
      (print "Got AST: \n";
       PrintAbsyn.print (TextIO.stdOut, actual);
       false)

fun checkType (NONE, _) = true
  | checkType (SOME expected, actual : Types.ty) =
    if Types.equalTy expected actual then
      true
    else
      (print (ErrorMsg.mkStr 0 ("TestFailure: Type: expected " ^
                                Types.toString expected ^
                                ", got " ^
                                Types.toString actual));
       false)

fun test {name, source,
          parse=(ast, parse_errors),
          check=(ty, check_errors)} =
    let
      val _ = (print ("Running test " ^ name ^ "...\n"); ErrorMsg.reset name)
      val actual_ast = Parse.parse (name, source)
      val passed = checkAst (ast, actual_ast) andalso (checkErrors parse_errors)
      val continue = case parse_errors of
                       SOME e => (length e = 0)
                     | NONE => true
      (* Semant processing is delayed until after calling checkErrors on the
       * parse phase b/c checkErrors clears the error log and that would prevent
       * us from testing type errors. *)
      (* val {exp=_, ty=actual_type} = Semant.transProg actual_ast *)
      val passed = passed andalso continue andalso
                   (checkType (ty, #ty (Semant.transProg actual_ast))) andalso
                   (checkErrors check_errors)
    in
      (print "\n"; passed)
    end

end

structure Tests =
struct

structure T = Types
val s = Symbol.symbol

(* Generate new test cases easily by running:
 * (Tiger.compileFile "test.tig"; !ErrorMsg.errorLog),
 * this shows you the error messages *with* positions,
 * also be sure to set Control.Print.printDepth high *)

val filetests =
    [{file="test1.tig",
      parse=(NONE : Absyn.exp option, SOME []),
      check=(SOME (T.ARRAY (T.INT, 1, 49)), SOME [])},

     (* a) This test case should have no errors.
      * b) If this test case were an error, some errors could be
      *    avoided by evaluating the array's element type to unit
      *    and then suppressing subsequent errors. See test case below. *)
     {file="test2.tig",
      parse=(NONE, SOME []),
      check=(SOME (T.ARRAY (T.INT, 1, 79)), SOME [])},

     {file="test3.tig",
      parse=(NONE, SOME []),
      check=(SOME (T.RECORD ([(s "name", T.STRING),
                              (s "age", T.INT)], 49)),
             SOME [])},

     {file="test4.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test5.tig",
      parse=(NONE, SOME []),
      check=let val link = ref NONE
              val record = (T.RECORD ([(s "hd", T.INT),
                                       (s "tl", Types.NAME (s "intlist", link))], 61))
              val _ = link := SOME record
            in
              (SOME record, SOME [])
            end},

     {file="test6.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {file="test7.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test8.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     (* TODO: check if branches are reversed, ie string then int should eval to string/top? *)
     {file="test9.tig",
      parse=(NONE, SOME []),
      check=(SOME T.TOP, SOME [Error.IfBranchMismatch {pos=68, then'=T.INT, else'=T.STRING}])},

     {file="test10.tig",
      parse=(NONE,
             SOME []),
      check=(NONE,
             SOME [Error.NonUnitWhile {pos=56, actual=Types.INT}])},

     {file="test11.tig",
      parse=(NONE, SOME []),
      check=(NONE,
             SOME [Error.ForRangeMismatch {pos=92, actual=Types.STRING, which="upper"}
     (* todo: is the index variable assignment supposed to be caught? *)])},

     {file="test12.tig",
      parse=(NONE, SOME []),
      check=(SOME Types.UNIT, SOME [])},

     {file="test13.tig",
      parse=(NONE, SOME []),
      check=(SOME Types.INT, SOME [Error.OperandMismatch {pos=53,
                                                          expected=Types.INT,
                                                          actual=Types.STRING,
                                                          oper=Absyn.GtOp}])},

     {file="test14.tig",
      parse=(NONE, SOME []),
      check=(SOME Types.INT,
             SOME [Error.OperandMismatch {pos=199,
                                          expected=Types.RECORD ([(s "name", T.STRING),
                                                                  (s "id", T.INT)], 75),
                                          actual=T.ARRAY (T.INT, 1, 46),
                                          oper=Absyn.NeqOp}])},

     {file="test15.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.NonUnitIf {pos=53, actual=T.INT}])},

     {file="test16.tig",
      parse=(NONE, SOME []),
      check=(SOME T.STRING, SOME [Error.CyclicTypeDec {pos=87, syms=[s "a", s "b", s "c", s "d"]}])},

     {file="test17.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.UnresolvedType {pos=84, sym=s "treelist"}])},

     {file="test18.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.UndefinedFunction {pos=118, sym=s "do_nothing2"}])},

     {file="test19.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.UndefinedVar {pos=218, sym=s "a"}])},

     {file="test20.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.UndefinedVar {pos=55, sym=s "i"}])},

     {file="test21.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.NonUnitProcedure {pos=97, name=s "nfactor", body=T.INT},
                                Error.OperandMismatch {pos=159,
                                                       oper=Absyn.TimesOp,
                                                       actual=T.UNIT,
                                                       expected=T.INT}])},

     {file="test22.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.NoSuchField {pos=131, field=s "nam", record=T.RECORD ([(s "name", T.STRING),
                                                                                             (s "id", T.INT)], 48)}])},

     {file="test23.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.AssignmentMismatch {actual=T.STRING, expected=T.INT, pos=138},
                                Error.AssignmentMismatch {actual=T.INT, expected=T.STRING, pos=121}])},

     {file="test24.tig",
      parse=(NONE, SOME []),
      check=(SOME T.TOP, SOME [Error.NonArrayAccess {actual=T.INT, pos=54}])},

     {file="test25.tig",
      parse=(NONE, SOME []),
      check=(SOME T.TOP, SOME [Error.NonRecordAccess {pos=55, field=s "f", actual=T.INT}])},

     {file="test26.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.OperandMismatch {pos=38, oper=Absyn.PlusOp, actual=T.STRING, expected=T.INT}])},

     {file="test27.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test28.tig",
      parse=(NONE, SOME []),
      check=let val rectype1 = T.RECORD ([(s "name", T.STRING),
                                          (s "id", T.INT)], 45)
              val rectype2 = T.RECORD ([(s "name", T.STRING),
                                        (s "id", T.INT)], 85) in
              (SOME rectype1, SOME [Error.AssignmentMismatch {pos=126, expected=rectype1, actual=rectype2}])
            end},

     {file="test29.tig",
      parse=(NONE, SOME []),
      check=let val arrtype1 = T.ARRAY (T.INT, 1, 44)
              val arrtype2 = T.ARRAY (T.INT, 1, 74) in
              (SOME arrtype1, SOME [Error.AssignmentMismatch {pos=105, expected=arrtype1, actual=arrtype2}])
            end},

     {file="test30.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test31.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.AssignmentMismatch {pos=60, actual=T.STRING, expected=T.INT}])},

     {file="test32.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.ArrayInitMismatch {pos=116, actual=T.STRING, expected=T.INT}])},

     (* Should the bad rectype {} expression be substituted with NIL or TOP? *)
     {file="test33.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.UnboundRecordType {pos=42, sym=s "rectype"}])},

     {file="test34.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.ArgumentMismatch {pos=106, actual=T.STRING, expected=T.INT}])},

     {file="test35.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.ArityMismatch {pos=93, actual=1, expected=2, name=s "g"},
                               Error.ArgumentMismatch {pos=95, actual=T.STRING, expected=T.INT}])},

     {file="test36.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.ArityMismatch {pos=94, actual=3, expected=2, name=s "g"}])},

     {file="test37.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test38.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.TypeRedefined {pos=176, name=s "a"}])},

     {file="test39.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.FunRedefined {pos=194, name=s "g"}])},

     {file="test40.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.NonUnitProcedure {pos=45, name=s "g", body=T.INT}])},

     {file="test41.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test42.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {file="test43.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.OperandMismatch {pos=90, oper=Absyn.PlusOp, actual=T.UNIT, expected=T.INT}])},

     {file="test44.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     (* expected output? *)
     {file="test45.tig",
      parse=(NONE, SOME []),
      check=(SOME T.NIL, SOME [Error.NilInitialization {pos=120, name=s "a"}])},

     {file="test46.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test47.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test48.tig",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {file="test49.tig",
      parse=(NONE, SOME [Error.Parse {pos=130, msg="syntax error: inserting  PLUS"}]),
      check=(NONE, NONE)},

     {file="queens.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {file="index.tig",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.DimensionMismatch {pos=86,
                                                         actual=1,
                                                         expected=2,
                                                         ty=T.ARRAY (T.INT, 2, 8)},
                                Error.NonIntSubscript {pos=122, actual=T.UNIT}])}]

val nonfiletests =
    [{name="1", source="let type a = {a: int} var a := a{} in 0 end",
      parse=(NONE, SOME []),
      check=(NONE, SOME [Error.MissingField {field=s "a", pos=33, expected=T.INT}])},

     {name="2", source="let type a = {a: int} var a := a{a=5} in a.b end",
      parse=(NONE, SOME []),
      check=(NONE, SOME [Error.NoSuchField {field=s "b", pos=43, record=T.RECORD ([(s "a", T.INT)], 6)}])},

     {name="3", source="1\\",
      parse=(SOME (Absyn.IntExp (1, 2)),
             SOME [Error.Lex {pos=3, msg="Illegal character: \\"}]),
      check=(SOME Types.INT, SOME [])},

     {name="4", source="let type arrtype = array of int var a : arrtype := arrtype[0] of 0 in a end",
      parse=(NONE, SOME []),
      check=(SOME (T.ARRAY (T.INT, 1, 6)), SOME [])},

     (* test seqs *)
     {name="5", source="(5; \"foo\"; ())",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     (* TODO: dedupe errors *)
     {name="6", source="let function foo(x : num) = () in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.UnboundType {pos=19, sym=s "num"}])},

     {name="7", source="let var a : num := 5 in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.UnboundType {pos=14, sym=s "num"}])},

     {name="8", source="let var a : int := foo in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.UndefinedVar {pos=21, sym=s "foo"}])},

     {name="9", source="let var a : int := 5 in a := \"\" end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.AssignmentMismatch {pos=26, expected=T.INT, actual=T.STRING}])},

     {name="10", source="break",
      parse=(NONE, SOME []),
      check=(SOME T.BOTTOM, SOME [Error.IllegalBreak {pos=2}])},

     {name="11", source="while 1 do (1 + break; ())",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {name="12", source="let var myarr := arr[10] of 1 in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.UnboundType {pos=19, sym=s "arr"}])},

     {name="13", source="let type rec = {a: int} type arr = array of rec var a := arr[10] of nil in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {name="14", source="if 1 then let type rec = {} in rec{} end else rec{}",
      parse=(NONE, SOME []),
      check=(SOME T.TOP, SOME [Error.UnboundRecordType {pos=48, sym=s "rec"}])},

     (* Should programs with type errors such as this be TOP instead? *)
     {name="15", source="let type arr = array of int var myarr := arr[10] of 0 in myarr[()] end",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [Error.NonIntSubscript {pos=65, actual=T.UNIT}])},

     (* TODO: is this actually legal? *)
     {name="16", source="while 1 do let function f() = (break; ()) in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [Error.IllegalBreak {pos=33}])},

     {name="17", source="while 1 do let var a := break in () end",
      parse=(NONE, SOME []),
      check=(SOME T.UNIT, SOME [])},

     {name="18", source="a[0]",
      parse=(NONE, SOME []),
      check=(SOME T.TOP, SOME [Error.UndefinedVar {pos=2, sym=s "a"}])},

     {name="19", source="nil = nil",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {name="20", source="let function foo(foo: int) : int = foo in foo(4) end",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {name="21", source="5 + exit(0)",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {name="22", source="\"foo\"=\"bar\"",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME [])},

     {name="23", source="\"foo\"=5",
      parse=(NONE, SOME []),
      check=(SOME T.INT, SOME[Error.OperandMismatch{pos=8,
                                                    expected=T.STRING,
                                                    actual=T.INT,
                                                    oper=Absyn.EqOp}])},

    {name="24", source="\"foo\" < \"quux\"",
     parse=(NONE, SOME []),
     check=(SOME T.INT, SOME [])},

    {name="25", source="let type rec = {} var a := rec {} var b := rec {} in a < b end",
     parse=(NONE, SOME []),
     check=(SOME T.INT, SOME[Error.OperandMismatch{pos=55,
                                                   expected=T.INT,
                                                   actual=T.RECORD ([], 6),
                                                   oper=Absyn.LtOp}])},

    {name="26", source="let type r = {a: int} var b := r {a=1, a=2} in () end",
     parse=(NONE, SOME []),
     check=(SOME T.UNIT, SOME[Error.DuplicateField{pos=33,
                                                   field=s "a"}])}]

fun run () =
    let val results = List.concat [(map (fn {file, parse, check} =>
                                      let val file = "testcases/" ^ file in
                                        Tester.test {name=file,
                                                     source=TextIO.openIn file,
                                                     parse=parse,
                                                     check=check}
                                      end)
                                  filetests),

                             (* Non-file tests *)
                             (map (fn {name, source, parse, check} =>
                                      Tester.test {name=name,
                                                   source=TextIO.openString source,
                                                   parse=parse,
                                                   check=check})
                                  nonfiletests)]
      val passedCount = length (List.filter (fn result => result = true) results)
    in
      print (Int.toString passedCount ^ "/" ^ Int.toString (length results) ^ " tests passed.\n")
    end

end

fun newInst (dst, src) =
    Assem.OPER {assem="", dst=dst, src=src, jump=NONE}

fun newMove (dst, src) =
    Assem.MOVE {assem="", dst=dst, src=src}

val instrs = let
  val L1 = Temp.newLabel ()
  val a = Temp.newTemp ()
  val b = Temp.newTemp ()
  val c = Temp.newTemp ()
in
  [newInst ([a], []),
   Assem.LABEL {assem="", lab=L1},
   newInst ([b], [a]),
   newInst ([c], [c, b]),
   newInst ([a], [b]),
   Assem.OPER {assem="", dst=[], src=[a], jump=SOME [L1]},
   newInst ([], [c])]
end

val instrs'' = let
  val enter = Temp.newLabel ()
  val loop = Temp.newLabel ()
  val cont = Temp.newLabel ()
  val r1 = Temp.newTemp ()
  val r2 = Temp.newTemp ()
  val r3 = Temp.newTemp ()
  val a = Temp.newTemp ()
  val b = Temp.newTemp ()
  val c = Temp.newTemp ()
  val d = Temp.newTemp ()
  val e = Temp.newTemp ()
in
  [Assem.LABEL {assem="", lab=enter}, (* n0 *)
   newMove (c, r3), (* n1 *)
   newMove (a, r1), (* n2 *)
   newMove (b, r2), (* n3 *)
   newInst ([d], []), (* n4 *)
   newMove (e, a), (* n5 *)

   Assem.LABEL {assem="", lab=loop}, (* n6 *)
   newInst ([d], [d, b]), (* n7 *)
   newInst ([e], [e]), (* n8 *)
   Assem.OPER {assem="", dst=[], src=[e], jump=SOME [loop, cont]}, (* n9 *)
   Assem.LABEL {assem="", lab=cont}, (* n10 *)
   newMove (r1, d), (* n11 *)
   newMove (r3, c), (* n13 *)
   newInst ([], [r1, r3]) (* n14 *) (* r1, r3 live out *)]
end;

(*

 val (graph, nodes) = MakeGraph.instrs2graph instrs'';
 val (igraph, liveout) = Liveness.interferenceGraph graph;

 print "\nInterferences:\n";
 Liveness.show (TextIO.stdOut, igraph);

 print "\nLiveout:\n";
 app (fn n => print ("- " ^ String.concatWith ", " (map Int.toString (liveout n)) ^ "\n")) nodes;
 (* Print all def's *)
 val Flow.FGRAPH {control, def, use, ismove} = graph;
 app (fn n => print ("- " ^ String.concatWith ", "
                                              (map Int.toString
                                                   (Temp.Set.listItems (Flow.Graph.Table.get (def, n, "")))) ^ "\n"))
     nodes;
 *)

(* Actual liveouts:
- 155, 156, 157
- 155, 156, 160
- 156, 158, 160
- 158, 159, 160
- 158, 159, 160, 161
- 159, 160, 161, 162
- 159, 160, 161, 162
- 159, 160, 161, 162
- 159, 160, 161, 162
- 159, 160, 161, 162
- 160, 161
- 155, 160
- 155, 157 *)

val instrs' = let
  val L1 = Temp.newLabel ()
  val L2 = Temp.newLabel ()
  val L3 = Temp.newLabel ()
  val L4 = Temp.newLabel ()
  val a = Temp.newTemp ()
  val b = Temp.newTemp ()
  val c = Temp.newTemp ()
  val d = Temp.newTemp ()
  val e = Temp.newTemp ()
  val f = Temp.newTemp ()
in
  [newInst ([b], []),
   newInst ([a], []),
   newInst ([f], []),
   Assem.LABEL {assem="", lab=L1},
   Assem.OPER {assem="", dst=[], src=[a, b], jump=SOME [L2, L3]},

   Assem.LABEL {assem="", lab=L2},
   newInst ([c], [a, b]),
   newInst ([d], [c]),
   newInst ([f], [d]),
   newInst ([e], [c]),
   newInst ([f], [e]),
   newInst ([b], [f]),
   Assem.OPER {assem="", dst=[], src=[], jump=SOME [L4]},

   Assem.LABEL {assem="", lab=L3},
   newInst ([f], [f, a, b]),
   Assem.OPER {assem="", dst=[], src=[], jump=SOME [L4]},

   Assem.LABEL {assem="", lab=L4},
   newInst ([a], [a]),
   Assem.OPER {assem="", dst=[], src=[], jump=SOME [L1]}]
end;

(* Actual interference graph:
a: f, e, d, c, b
b: f, a
c: f, d, a
d: c, a
e: a
f: c, b, a *)

(* Need to remove the signature of Liveness for this to work *)
(*
val (flowgraph, nodes) = MakeGraph.instrs2graph instrs
val (lin, lout) = Liveness.livenessGraph flowgraph
val _ = app (fn s =>
                print (String.concatWith ", "
                                         (map Int.toString
                                              (Liveness.Temp.Set.listItems s)) ^ "\n"))
            (map (fn n =>
                     (valOf (Liveness.T.look (lout, n)))) nodes)
*)

(* Callee save register code alone doubles the queens compile time. *)
(*

let val timer = Timer.startCPUTimer (); val _ = Tiger.compileFile "testcases/merge.tig" in Timer.checkCPUTimer timer end

val g = Graph.newGraph ();
val nodes as [n0, n1, n2, n3] = List.tabulate (4, (fn _ => Graph.newNode g))
val _ = (Graph.mk_edge {from=n0, to=n1};
         Graph.mk_edge {from=n0, to=n2};
         Graph.mk_edge {from=n1, to=n2};
         Graph.mk_edge {from=n1, to=n3};
         Graph.mk_edge {from=n3, to=n0} (* add cycle *)
        )

String.concatWith ", " (map Graph.nodename nodes)
*)
