structure VM (*: sig val x : int end*) = struct

structure T = Tree

(* TODO: Should come up with a new continuation variable to differentiate
 * between continuations that take only stores, and continuations that
 * take a value and a store *)

datatype value = INT of int
               | LABEL of Temp.label

(* Exprs can no longer evaluate to temps...
 * this was only necessary for move insns, where we now match the label *)

fun doRelop (relop, INT n1, INT n2) =
    (case relop of
       T.EQ => op=
     | T.NE => op<>
     | T.LT => Int.<
     | T.LE => Int.<=
     | T.GT => Int.>
     | T.GE => Int.>=
    (* Unsigned comparison requires use of Word *)
     | _ => raise Fail "Comparator not implemented yet")
      (n1, n2)
  | doRelop _ = raise Fail "Cannot compare non-integers"

fun doBinop (binop, INT n1, INT n2) =
    (case binop of
       T.PLUS => Int.+
     | T.MINUS => Int.-
     | T.MUL => Int.*
     | T.DIV => Int.div
    (* Bitwise operations requires use of Word *)
     | _ => raise Fail "Operator not implemeneted yet")
    (n1, n2)
  | doBinop (_, INT _, LABEL l) = raise Fail ("Cannot perform arithmetic on non-integer: " ^ Symbol.name l)
  | doBinop (_, LABEL l, INT _) = raise Fail ("Cannot perform arithmetic on non-integer: " ^ Symbol.name l)
  | doBinop _ = raise Fail "Cannot perform arithmetic on non-integers."

datatype store = Store of (Temp.temp -> value) *
                          (int -> value) *
                          (Temp.label -> (store -> store))

(*
type table = (Temp.label * (store -> store)) list
type stmK = store -> store
type expK = value * store -> store
*)

fun labelsToStore table =
    let
      val code = foldr (fn ((label, k), code) =>
                           (fn label' =>
                               if label' = label then
                                 k
                               else
                                 code label'))
                       (fn l => raise Fail ("label undefined: " ^ Symbol.name l))
                       table
    in
      Store ((fn reg => raise Fail ("reg undefined: " ^ Int.toString reg)),
             (fn addr => raise Fail ("addr undefined: " ^ Int.toString addr)),
             code)
    end

(* The stack and heap both obviously live in memory,
 * to avoid conflicts we will have the stack grow down
 * from -1. The heap will grow up from 1. The 0 memory
 * location is reserved for null pointers. This also
 * relies on our calling convention moving the stack
 * pointer *down*. *)
fun getReg (Store (reg, _, _)) tmp = (reg tmp)
fun getMem (Store (_, mem, _)) addr = (mem addr)
fun getLabel (Store (_, _, code)) label = (code label)

fun valToStr (INT n) = Int.toString n
  | valToStr (LABEL l) = Symbol.name l

fun updateReg (Store (reg, mem, code)) (tmp, value) =
    (print ("R" ^ (Int.toString tmp) ^ " <- " ^ (valToStr value) ^ "\n");
     Store ((fn tmp' => if tmp' = tmp then value else reg tmp'), mem, code))
fun updateMem (Store (reg, mem, code)) (addr, value) =
    (print ("M" ^ (Int.toString addr) ^ " <- " ^ (valToStr value) ^ "\n");
     Store (reg, (fn addr' => if addr' = addr then value else mem addr'), code))

fun rewriteStm (T.SEQ (s1, s2)) = T.SEQ (rewriteStm s1, rewriteStm s2)
  | rewriteStm (T.JUMP (e, ls)) = T.JUMP (rewriteExp e, ls)
  | rewriteStm (T.CJUMP (r, e1, e2, l1, l2)) = T.CJUMP (r,
                                                        rewriteExp e1,
                                                        rewriteExp e2,
                                                        l1, l2)
  | rewriteStm (T.MOVE (e1, e2)) = T.MOVE (rewriteExp e1, rewriteExp e2)
  | rewriteStm (T.EXP e) = T.EXP (rewriteExp e)
  | rewriteStm (T.LABEL l) = T.LABEL l

and rewriteExp (T.BINOP (b, e1, e2)) = T.BINOP (b,
                                                rewriteExp e1,
                                                rewriteExp e2)
  | rewriteExp (T.MEM e) = T.MEM (rewriteExp e)
  | rewriteExp (T.TEMP t) = T.TEMP t
  | rewriteExp (T.ESEQ (s, e)) = T.ESEQ (rewriteStm s, rewriteExp e)
  | rewriteExp (T.NAME l) = T.NAME l
  | rewriteExp (T.CONST n) = T.CONST n
  | rewriteExp (T.CALL (exp, exps)) = Frame.rewriteCall (exp, exps)

(* k is the actual continuation: store -> v *)
fun stmToCps (T.SEQ (s1, s2)) (k, t) =
    stmToCps s1 (stmToCps s2 (k, t))
  | stmToCps (T.LABEL l) (k, t) =
    (k, (l, k) :: t)
  | stmToCps (T.JUMP (exp, _)) (k, t) =
    let
      (* look up the continuation for label and call that continuation with store *)
      fun k' (LABEL label, store) =
          ((getLabel store label) store)
        | k' _ = raise Fail "cannot jump to non-label"
    in
      expToCps exp (k', t)
    end
  | stmToCps (T.MOVE (T.TEMP locTmp, valExp)) (k, t) =
    let
      fun k1 (value, store) =
           k (updateReg store (locTmp, value))
    in
      (* expToCps needs to return an expression that will take a store,
       * and call the continuation expression *with* an updated store
       * (updated by any side effects of evaluating the expression)
       * and the value of the eval'd expr.
       * This means that expToCps and stmToCps have the same return
       * type, only different argument types. *)
      expToCps valExp (k1, t)
    end
  | stmToCps (T.MOVE (T.MEM locExp, valExp)) (k, t) =
    let
      val locTmp = Temp.newTemp ()

      fun k2 (value, store) =
          let val addr = case getReg store locTmp of
                           INT addr => addr
                         | _ => raise Fail "Cannot store to non-addr in memory"
          in
            k (updateMem store (addr, value))
          end
      val (k', t') = expToCps valExp (k2, t)

      fun k1 (loc, store) =
          k' (updateReg store (locTmp, loc))
    in
      expToCps locExp (k1, t')
    end
  | stmToCps (T.MOVE _) _ = raise Fail "Illegal move operands"
  | stmToCps (T.EXP exp) (k, t) =
    let
      fun k1 (_, store) =
          k store
    in
      expToCps exp (k1, t)
    end
  | stmToCps (T.CJUMP (relop, e1, e2, l1, l2)) (k, t) =
    let
      val v1Tmp = Temp.newTemp ()

      fun k2 (v2, store) =
          let
            val v1 = (getReg store v1Tmp)
            val result = doRelop (relop, v1, v2)
          in
            if result then
              ((getLabel store l1) store)
            else
              ((getLabel store l2) store)
          end
      val (k', t') = expToCps e2 (k2, t)

      fun k1 (v1, store) =
          k' (updateReg store (v1Tmp, v1))
    in
      expToCps e1 (k1, t')
    end

and expToCps (T.MEM exp) (k, t) =
    let
      fun k1 (INT addr, store) =
          k ((getMem store addr), store)
        | k1 _ = raise Fail "Cannot dereference non-address"
    in
      expToCps exp (k1, t)
    end
  | expToCps (T.TEMP tmp) (k, t) =
    let
      fun k' store =
          k (getReg store tmp, store)
    in
      (k', t)
    end
  | expToCps (T.ESEQ (stm, exp)) (k, t) =
    stmToCps stm (expToCps exp (k, t))
  | expToCps (T.NAME label) (k, t) =
    let
      fun k' store =
          k (LABEL label, store)
    in
      (k', t)
    end
  | expToCps (T.CONST n) (k, t) =
    let
      fun k' store =
          k (INT n, store)
    in
      (k', t)
    end
  | expToCps (T.CALL (exp, exps)) (k, t) =
    (* eval the callsite and then eval the args *)
    (* need a calling convention: a function that takes a
     * number and returns a list of places (tmps or mem) to save arguments
     * the mems would be *)
    (* Only constraint we place on rewriteCall is that it should
     * leave RV untouched? - not even so, just have rewrite return another exp *)
    let
      (* val returnLabel = Temp.newLabel () *)
      (* create a label and save the continuation for that label
       * into the store, then pass that label as the return addr *)
      (* rewrite the call and then cps transform the new tree *)
      (* rewrite must remove the CALL from the tree *)
      (* val callExp = rewriteCall (exp, exps) *)
      (* need to write a new continuation that will pull
       * the RV and pass that to the continuation? *)
      (* fun k' (store) =
          k (getReg store Translate.Frame.RV, store) *)
    in
      (* the mips call implementation will, for instance, say
       * to write args > 4 to a position relative to the *stack*
       * pointer. But we also need to update the SP and FP... hrm *)
      raise Fail "encountered call in conversion";
      expToCps (Frame.rewriteCall (exp, exps)) (k, t)
    end
  | expToCps (T.BINOP (binop, e1, e2)) (k, t) =
    let
      val v1Tmp = Temp.newTemp ()

      fun k2 (v2, store) =
          let val v1 = (getReg store v1Tmp) in
            k (INT (doBinop (binop, v1, v2)), store)
          end
      val (k', t') = expToCps e2 (k2, t)

      fun k1 (v1, store) =
          k' (updateReg store (v1Tmp, v1))
    in
      expToCps e1 (k1, t')
    end

fun transFrags (Frame.PROC {body, frame} :: frags) =
    Frame.PROC {body=rewriteStm body, frame=frame} ::
    map (fn (Frame.PROC {body, frame}) =>
            Frame.PROC {body=Frame.rewriteBody (rewriteStm body, frame), frame=frame}
          | x => x)
        frags
  | transFrags _ = raise Fail "transFrags failed"

fun progToCps (main :: frags) =
    let
      val id = (fn x => x)
      val (_, t) = foldr (fn (Frame.PROC {body, frame}, (_, t)) =>
                             let
                               val (k, t') = stmToCps body (id, t)
                             in
                               (id, (Frame.name frame, k) :: t')
                             end
                             (* TODO: will need to eventually split the list and
                              * move the string labels into memory, replacing them with pointers? erg...
                              * or make the code store a sum type over strings and continuations... *)
                           | (Frame.STRING (label, str), (_, t)) => (id, t))
                         (id, [])
                         frags
      val (k, t) = case main of
                     Frame.PROC {body, frame} =>
                     stmToCps body (id, t)
                   | _ => raise Fail "main must be a proc"
      val str = foldr (fn ((r, v), str) =>
                          updateReg str (r, v))
                      (labelsToStore t)
                      [(Frame.FP, INT ~1),
                       (Frame.SP, INT ~1),
                       (Frame.RA, INT 0)]
    in
      (k, str)
    end
  | progToCps _ = raise Fail "no frags to convert!"

end

(* TODO: when translating frags, the frag needs a prologue that bumps the stack pointer *)

 (* Use:
val frags = #frags (Tiger.compileStr "let function foo(x: int): int = let function bar(y: int): int = x in bar(2) end in foo(5) end");
val [Translate.Frame.PROC {body=bMain, frame=fMain}, Translate.Frame.PROC {body=bFoo, frame=fFoo}, Translate.Frame.PROC {body=bBar, frame=fBar}] = frags;
val (k, str) = VM.progToCps frags;
val str' = k str;
VM.getReg str' Frame.RV
*)
