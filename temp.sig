signature TEMP =
sig
  eqtype temp
  val newTemp : unit -> temp
  structure Table : TABLE sharing type Table.key = temp
  structure Set : ORD_SET sharing type Set.Key.ord_key = temp
  val toString: temp -> string
  type label = Symbol.symbol
  val newLabel : unit -> label
  val namedLabel : string -> label
end

