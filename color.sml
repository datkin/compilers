(* We provide two backing implementations in a work list -
 * (1) as a set or (2) as a list. This is important because
 * for some collections in the worklists, order matters.
 * Specifically, the order in which nodes are added to
 * "select" matters, b/c "select" is a stack. *)
signature WORK_LISTS = sig
  type id
  type item
  type lists
  structure Set : ORD_SET sharing type Set.Key.ord_key = item

  datatype collection = List of item list
                      | Set of Set.set

  val asSet: lists -> id -> Set.set
  val asList: lists -> id -> item list
  val isMember: lists -> id -> item -> bool
  val isMember': lists -> item -> id -> bool
  val isEmpty: lists -> id -> bool
  val move: lists -> id -> id -> item -> lists
  val move': lists -> item -> id -> id -> lists
  val newId: string -> id
  val newLists: (id * collection) list -> lists

  val debug: (item -> string) * lists -> unit
(*
  val newWorklists: id list -> 'a worklists
  val add: 'a worklists -> id -> 'a -> 'a worklists
*)
end

functor WorkLists (structure Set : ORD_SET) : WORK_LISTS =
struct
type id = Symbol.symbol
type item = Set.item
structure Set = Set

datatype collection = List of item list
                    | Set of Set.set

type lists = collection Symbol.table

fun eq a b = Set.Key.compare (a, b) = General.EQUAL

fun get (lists, id) : collection =
    case Symbol.look (lists, id) of
      SOME collection => collection
    | NONE => raise Fail ("Lists doesn't contain " ^ (Symbol.name id))

fun asSet lists id =
    case get (lists, id) of
      List list => Set.addList (Set.empty, list)
    | Set set => set

fun asList lists id =
    case get (lists, id) of
      List list => list
    | Set set => Set.listItems set

fun isMember lists id item =
    case get (lists, id) of
      List list => List.exists (eq item) list
    | Set set => Set.member (set, item)

fun isMember' lists item id =
    case get (lists, id) of
      List list => List.exists (eq item) list
    | Set set => Set.member (set, item)

fun isEmpty lists id =
    case get (lists, id) of
      List list => List.null list
    | Set set => Set.isEmpty set

fun move lists srcId dstId item =
    let
      fun removeList (_, []) = raise Fail "item was not present (in list)"
        | removeList (item, item' :: rest) =
          if eq item item' then rest
          else item' :: (removeList (item, rest))

      fun removeSet (item, set) =
          (* TODO: this test *could* be removed? *)
          if Set.member (set, item) then
            Set.delete (set, item)
          else
            raise Fail "item was not present (in set)"

      fun remove (item, List list) = List (removeList (item, list))
        | remove (item, Set set) = Set (removeSet (item, set))

      val insertList = op::

      fun insertSet (item, set) = Set.add (set, item)

      fun insert (item, List list) = List (insertList (item, list))
        | insert (item, Set set) = Set (insertSet (item, set))

      val src = get (lists, srcId)
      val src' = remove (item, src)
      val dst = get (lists, dstId)
      (* TODO: validate the item wasn't already present? *)
      val dst' = insert (item, dst)
    in
      foldl Symbol.enter'
            lists
            [(srcId, src'), (dstId, dst')]
    end

fun move' lists item srcId dstId = move lists srcId dstId item

val newId = Symbol.symbol

fun newLists initials =
    foldr (fn ((id, initial), sets) =>
              Symbol.enter' ((id, initial),
                             sets))
          Symbol.empty
          initials

fun debug (toStr, wls) =
    let
      fun listToString list = String.concatWith ", " (map toStr list)
    in
      app (fn key =>
              (print (Symbol.name key ^ ": [");
               print (case Symbol.look (wls, key) of
                       SOME (List list) => listToString list
                     | SOME (Set set) => listToString (Set.listItems set)
                     | NONE => raise Fail "cannot to string!?");
                print "]\n"))
          (map #1 (Symbol.entries wls))
    end
end

structure Color : COLOR =
struct

structure GS = Graph.Set and GT = Graph.Table
(* Register Set *)
structure RS = BinarySetFn (type ord_key = string
                            val compare = String.compare)
structure NodeWL = WorkLists(structure Set = GS)
(* Move Set *)
structure MS = BinarySetFn (type ord_key = Temp.temp * Temp.temp
                            fun compare ((t1, t2), (t1', t2')) =
                                if t1 = t1' then
                                  Int.compare (t2, t2')
                                else
                                  Int.compare (t1, t1'))
structure MoveWL = WorkLists(structure Set = MS)

structure Id = struct
  val precolored = NodeWL.newId "precolored";
  val initial = NodeWL.newId "initial";
  val simplify = NodeWL.newId "simplify";
  val spill = NodeWL.newId "spill";
  val spilled = NodeWL.newId "spilled";
  val colored = NodeWL.newId "colored";
  val select = NodeWL.newId "select";
(*
val freeze = NodeWL.newId "freeze";
val coalesced = NodeWL.newId "coalesced";
*)
end

fun eq a b = a = b

fun toNodeSet list = GS.addList (GS.empty, list)

(* TODO: we'd save a lot of set -> list conversions if we
 * make this work natively on sets. *)
fun min ([], _) = raise Fail "cannot take min of empty list!"
  | min (first :: rest, f) =
    let
      val (item, _) =
          foldl (fn (item, (minItem, minVal)) =>
                    let val itemVal = f item in
                      if itemVal < minVal then
                        (item, itemVal)
                      else
                        (minItem, minVal)
                    end)
                (first, f first)
                rest
    in
      item
    end

structure Frame = MipsFrame
type allocation = Frame.register Temp.Table.table

fun color {interference = Liveness.IGRAPH {graph, tnode, gtemp, moves},
           initial, spillCost, registers} =
    let
      fun isPrecolored node =
          case Temp.Table.look (initial, gtemp node) of
            SOME _ => true
          | NONE => false

      val (precolored, uncolored) = List.partition isPrecolored
                                                   (Graph.nodes graph)

      val wls = NodeWL.newLists [(Id.precolored,
                                  NodeWL.Set (toNodeSet precolored)),
                                 (Id.initial,
                                  NodeWL.Set (toNodeSet uncolored)),
                                 (Id.simplify,
                                  NodeWL.Set (toNodeSet [])),
                                 (Id.spill,
                                  NodeWL.Set (toNodeSet [])),
                                 (Id.spilled,
                                  NodeWL.Set (toNodeSet [])),
                                 (Id.colored,
                                  NodeWL.Set (toNodeSet [])),
                                 (Id.select,
                                  NodeWL.List [])]

      val k = List.length registers

      val degrees = foldl GT.enter'
                          GT.empty
                          (map (fn node =>
                                   (node, List.length (Graph.adj node)))
                               uncolored)

      fun initWorklists (wls, degrees) =
          GS.foldl (fn (node, wls) =>
                    let
                      val moveTo = NodeWL.move' wls node Id.initial
                    in
                      if GT.get (degrees, node, "degree[n]") >= k then
                        moveTo Id.spill
                        (* TODO: case for freeze worklist *)
                      else
                        moveTo Id.simplify
                    end)
                   wls
                   (NodeWL.asSet wls Id.initial)

      val wls = initWorklists (wls, degrees)

      fun adjacent (node, wls) =
          foldl NodeWL.Set.difference
                (NodeWL.Set.addList (NodeWL.Set.empty, Graph.adj node))
                [NodeWL.asSet wls Id.simplify (*,
                 NodeWL.toSet wls Id.coalesced *)]

      val aliases = GT.empty

      fun getAlias (node, aliases, wls) =
          (* TODO: coalescing check *)
          (*
           if NodeWL.isMember wls Id.coalescedNodes then
            getAlias (GT.get (aliases, node, "alias[n]"),
                      aliases, wls)
          else *)
            node

      fun decrement (node, (wls, degrees)) =
          let
            val degree = GT.get (degrees, node, "degree[n]")
            val degrees' = GT.enter (degrees, node, degree - 1)
            val wls' = if degree = k then
                         (* TODO: case for move related *)
                         NodeWL.move wls Id.spill Id.simplify node
                       else
                         wls
          in
            (wls', degrees')
          end

      fun simplify (wls, degrees) =
          case NodeWL.asList wls Id.simplify of
            [] => (wls, degrees)
          | node :: _ =>
            (* TODO: does the order in which the stack is colored matter? *)
            let val wls' = NodeWL.move wls Id.simplify Id.select node in
              NodeWL.Set.foldl decrement
                               (wls', degrees)
                               (adjacent (node, wls'))
            end

      fun selectSpill (wls, degrees) =
          let
            val m = min (NodeWL.asList wls Id.spill, spillCost)
          in
            (* TODO: freezeMoves m *)
            (NodeWL.move wls Id.spill Id.simplify m,
             degrees)
          end

      fun loop (wls, degrees) =
          let
            fun notEmpty id = not (NodeWL.isEmpty wls id)
          in
            if notEmpty Id.simplify then
              loop (simplify (wls, degrees))
            (* TODO: Coalesce *)
            (* TODO: Freeze *)
            else if notEmpty Id.spill then
              loop (selectSpill (wls, degrees))
            else
              (wls, degrees) (* done *)
          end

      val _ = NodeWL.debug (Frame.tempToRegister o gtemp, wls)

      val (wls, degrees) = loop (wls, degrees)

      val _ = print ("Colors: " ^ (String.concatWith ", " registers))

      val colors = RS.addList (RS.empty, registers)

      fun getColor (node, allocs) =
          Temp.Table.get (allocs, gtemp node, "color[n]")

      fun setColor (node, color, allocs) =
          Temp.Table.enter (allocs, gtemp node, color)

      fun assignColors (wls, allocs) =
          case NodeWL.asList wls Id.select of
            (* TODO: color coalesced nodes *)
            [] => (wls, allocs)
          | node :: _ =>
            let
              fun neighborColor node =
                  let
                    (* TODO: pass in aliases *)
                    val node = getAlias (node, aliases, wls)
                    val isMember = NodeWL.isMember' wls node
                  in
                    if isMember Id.colored orelse
                       isMember Id.precolored then
                      SOME (getColor (node, allocs))
                    else
                      NONE
                  end

              val usedColors =
                  RS.addList (RS.empty,
                              List.mapPartial neighborColor
                                              (Graph.adj node))

              val okColors = RS.difference (colors, usedColors)

              val (wls', allocs') =
                  case RS.listItems okColors of
                    [] => (NodeWL.move wls Id.select Id.spilled node,
                           allocs)
                  | color :: _ => (NodeWL.move wls Id.select Id.colored node,
                                   setColor (node, color, allocs))

              val _ = print "\n"
              val _ = NodeWL.debug (Frame.tempToRegister o gtemp, wls')
              val _ = print ("Allocations: " ^
                             String.concatWith ", "
                             (map (fn key =>
                                      Temp.toString key ^ ": " ^
                                      Temp.Table.get (allocs', key, "!!!"))
                                  (map #1 (Temp.Table.entries allocs'))) ^
                            "\n")

            in
              assignColors (wls', allocs')
            end

      val (wls, allocs) = assignColors (wls, initial)

      val spills = map gtemp (NodeWL.asList wls Id.spilled)
    in
      (allocs, spills)
    end
end
