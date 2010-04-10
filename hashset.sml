structure HashSet : ORD_SET =
struct

structure Key : ORD_KEY = struct type ord_key = int val compare = Int.compare end

type item = Key.ord_key

structure Table = IntMapTable(type key = item
fun getInt n = n
fun getKey n = n)

(* TODO: replace all ((_, items) : set) code with (listItems set) calls *)
(* Removing items requires insert NONE *)
type set = unit option Table.table * item list

val empty = (Table.empty, [])

fun singleton item =
    (Table.enter (Table.empty, item, SOME ()), [item])

fun member ((table, _), item) =
    case Table.look (table, item) of
      SOME (SOME ()) => true
    | _ => false

fun add (set as (table, list), item) =
    if member (set, item) then
      set
    else
      (Table.enter (table, item, SOME ()), item :: list)

fun add' (item, set) = add (set, item)

fun addList (set, items) = List.foldl add' set items

fun delete ((table, list), item) =
    let
      (* We assume the item only appears once in the list *)
      fun removeFirst (x, nil) = nil
        | removeFirst (x, hd :: tail) =
          if x = hd then tail
          else hd :: (removeFirst (x, tail))
    in
      (Table.enter (table, item, NONE), removeFirst (item, list))
    end

fun isEmpty (_, []) = true
  | isEmpty _ = false

fun isSubset ((_, sublist), super) =
    List.all (fn item => member (super, item)) sublist

fun numItems (_, list) = length list

fun equal (set1, set2) =
    numItems set1 = numItems set2 andalso isSubset (set1, set2)

fun listItems (_, list) = list

fun map f ((_, items) : set) =
    List.foldl (fn (item, set) => add (set, f item))
               empty
               items

fun app f ((_, items) : set) =
    List.app f items

(* NB: set "ordering" is determined by the order of insertion *)
fun foldl f base ((_, list) : set) = List.foldl f base list

fun foldr f base ((_, list) : set) = List.foldr f base list

fun filter pred ((_, list) : set) =
    List.foldl (fn (item, set) =>
                   if pred item then add (set, item)
                   else set)
               empty
               list

fun exists pred ((_, list) : set) = List.exists pred list

fun find match ((_, list) : set) = List.find match list

fun union (set1, set2) = foldl add' set2 set1

fun intersection (set1, set2) =
    filter (fn item => member (set1, item))
           set2

fun difference (set1, set2) =
    let
      val union = union (set1, set2)
      val intersection = intersection (set1, set2)
    in
      filter (fn item => not (member (intersection, item)))
             union
    end

fun fromList list =
    List.foldr add' empty list

fun partition p set =
    foldl (fn (item, (A, B)) =>
              if p item then
                (add (A, item), B)
              else
                (A, add (B, item)))
          (empty, empty)
          set

(* ??? *)
fun compare (A, B) =
    case Int.compare (numItems A, numItems B) of
      General.EQUAL => Int.compare (numItems (union (A, B)),
                                    numItems B)
    | other => other

end
