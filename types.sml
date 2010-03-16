structure Types =
struct

  (* Use an integer to test type equality. This allows us to test
   * type equality. In practice we will use the declaration position
   * of a type as the unique type identifier. *)
  type unique = int (* unit ref *)

  datatype ty = NIL
              | INT
              | UNIT
              | STRING
              | ARRAY of ty * int * unique
              | NAME of Symbol.symbol * ty option ref
              | RECORD of (Symbol.symbol * ty) list * unique
              (* Types for the type lattice: *)
              | TOP
              | BOTTOM

  fun equalTy ty1 ty2 =
      let
        fun contains (rfs, rf : ty option ref) = List.exists (fn rf' => rf = rf') rfs
        fun safeEqualTy (NIL, NIL, _) = true
          | safeEqualTy (INT, INT, _) = true
          | safeEqualTy (UNIT, UNIT, _) = true
          | safeEqualTy (STRING, STRING, _) = true
          | safeEqualTy (TOP, TOP, _) = true
          | safeEqualTy (BOTTOM, BOTTOM, _) = true
          | safeEqualTy (ARRAY (_, _, unique1), ARRAY (_, _, unique2), _) = unique1 = unique2
          | safeEqualTy (RECORD (_, unique1), RECORD (_, unique2), _) = unique1 = unique2
          (* The only recursive calls occur on NAME types, so infinite loops can
           * only occur for cyclic NAMEs (ie we do not traverse a record's
           * fields checking for equality so this cannot cause infinite
           * recursion). This is the only place where updating and checking
           * the seen type list is necessary. If a type is seen twice there
           * is a cycle and the types are not equal (pathological case).
           *
           * For more robust checking it might be useful to compare the
           * uniqueness of types as well as to explicitly check their
           * fields. However, this complicates cycle checking. *)
          | safeEqualTy (NAME (_, tyref), ty2, seen) =
            (not (contains (seen, tyref)) andalso
             case !tyref of
               NONE => false
             | SOME ty1 => safeEqualTy (ty1, ty2, tyref :: seen))
          | safeEqualTy (ty1, NAME (_, tyref), seen) =
            (not (contains (seen, tyref)) andalso
             case !tyref of
               NONE => false
             | SOME ty2 => safeEqualTy (ty1, ty2, tyref :: seen))
          | safeEqualTy (_, _, _) = false
      in
        safeEqualTy (ty1, ty2, [])
      end

  (* This should be called in any context where we would expect all types to have
   * been resolved (ie, (mutually) recursive types have been linked) and we need to
   * have a Type that is not a name (ie, a type we can reason about with joins, etc)
   * We know we need to "force" a type when we begin comparing types *)
  fun actualTy (NAME (name, tyref))=
      (case !tyref of
         NONE => raise Fail ("Type not bound: " ^ (Symbol.name name))
       | SOME ty => ty)
    | actualTy ty = ty

  fun join (t1, BOTTOM) = t1
    | join (BOTTOM, t2) = t2
    | join (_, TOP) = TOP
    | join (TOP, _) = TOP
    | join (NIL, record as RECORD _) = record
    | join (record as RECORD _, NIL) = record
    | join (t1 as NAME _, t2) = join (actualTy t1, t2)
    | join (t1, t2 as NAME _) = join (t1, actualTy t2)
    | join (t1, t2) = if equalTy t1 t2 then t1 else TOP

  fun subtype t1 t2 = equalTy t2 (join (t1, t2));

  fun wellTyped t1 = t1 <> TOP;

  fun toString ty =
      let
        fun absent (ty : ty, tys) = not (List.exists (equalTy ty) tys)
        fun safeToString (NIL, _) = "nil"
          | safeToString (INT, _) = "int"
          | safeToString (UNIT, _) = "unit"
          | safeToString (STRING, _) = "string"
          | safeToString (TOP, _) = "Top"
          | safeToString (BOTTOM, _) = "Bottom"
          | safeToString (this as ARRAY (ty, dim, unique), seen) =
            "(" ^
            (String.concatWith " * " (List.tabulate (dim, (fn _ => "array")))) ^
            " of " ^ safeToString (ty, this :: seen) ^
            ", #" ^ Int.toString unique ^
            ")"

            (*
            if absent (this, seen) then
              "array(" ^ safeToString (ty, this :: seen) ^ ", "
              ^ Int.toString dim ^ ", #" ^ Int.toString unique ^ ")"
            else
              "<" ^ Int.toString unique ^ ">"
              *)
          | safeToString (this as NAME (sym, ty_ref), seen) =
            if absent (this, seen) then
              case !ty_ref of
                NONE => Symbol.name sym ^ "-?"
              | SOME ty => (Symbol.name sym) ^ "->" ^ safeToString (ty, this :: seen)
            else
              "<" ^ Symbol.name sym ^ ">"
          | safeToString (this as RECORD (fields, unique), seen) =
            if absent (this, seen) then
              let
                fun fieldToStr (sym, ty) =
                    (Symbol.name sym) ^ ": " ^
                    (safeToString (ty, this :: seen)) ^ ", "
                val fieldStrings = map fieldToStr fields
              in
                "record(" ^ String.concat fieldStrings ^ "#" ^ Int.toString unique ^ ")"
              end
            else
              "<" ^ Int.toString unique ^ ">"
      in
        safeToString (ty, [])
      end

end
