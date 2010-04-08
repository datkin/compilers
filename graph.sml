structure Graph :> GRAPH =
struct
type node' = int
type temp = Temp.temp

structure NodeSet = RedBlackSetFn (struct
                                   type ord_key = node'
                                   val compare = Int.compare
                                   end)

datatype noderep = NODE of {succ: NodeSet.set, pred: NodeSet.set}

val emptyNode = NODE{succ=NodeSet.empty, pred=NodeSet.empty}

(* Placed at the end of the array to indicate the end? *)
val bogusNode = NODE{succ=NodeSet.singleton ~1,
                     pred=NodeSet.empty}

fun isBogus(NODE{succ, pred}) = NodeSet.member (succ, ~1)

(* A graph is an array where each element is a NODE,
 * and a node contains the succ and pred lists. *)
structure A = DynamicArrayFn(struct open Array
			     type elem = noderep
			     type vector = noderep vector
			     type array = noderep array
                             end)

type graph = A.array

type node = graph * node'
fun eq ((_, a), (_, b)) = a=b

fun augment (g: graph) (n: node') : node = (g, n)

fun newGraph () = A.array (0, bogusNode)

fun nodes g =
    let
      (* Gives the index of the highest element that has been set in this array. *)
      val b = A.bound g
      fun f i = if isBogus (A.sub (g, i)) then
                  nil
		else
                  (g, i) :: f (i+1)
    in
      f 0
    end

fun succ (g, i) =
    let val NODE {succ, ...} = A.sub (g, i) in
      map (augment g) (NodeSet.listItems succ)
    end
fun pred (g, i) =
    let val NODE {pred, ...} = A.sub (g, i) in
      map (augment g) (NodeSet.listItems pred)
    end
fun adj (g, i) =
    let val NODE {succ, pred} = A.sub (g, i) in
      map (augment g) (NodeSet.listItems (NodeSet.union (succ, pred)))
    end

fun newNode g = (* binary search for unused node *)
    let fun look (lo, hi) =
            (* i < lo indicates i in use
             * i >= hi indicates i not in use *)
            if lo = hi then
              (A.update (g, lo, emptyNode); (g, lo))
            else let val m = (lo+hi) div 2 in
                   if isBogus (A.sub (g, m)) then
                     look (lo, m)
                   else
                     look (m+1, hi)
                 end
    in
      look (0, 1 + A.bound g)
    end

exception GraphEdge
fun check (g, g') = (* if g=g' then () else raise GraphEdge *) ()

val add = NodeSet.add'
fun delete (node, nodes) = NodeSet.delete (nodes, node)

fun diddle_edge change {from=(g:graph, i), to=(g':graph, j)} =
    let
      val _ = check(g, g')

      val NODE {succ=si, pred=pi} = A.sub (g, i)
      val _ = A.update (g, i, NODE{succ=change (j, si),
                                   pred=pi})

      val NODE{succ=sj, pred=pj} = A.sub (g, j)
      val _ = A.update (g, j, NODE{succ=sj,
                                   pred=change(i, pj)})
    in
      ()
    end

val mk_edge = diddle_edge add
val rm_edge = diddle_edge delete

structure Table = IntMapTable(type key = node
fun getInt (g, n) = n
fun getKey _ = raise Fail "getKey not supported")

fun nodename (g, i:int) = "n" ^ Int.toString(i)

end
