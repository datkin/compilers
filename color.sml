structure Color : COLOR =
struct

structure Frame = MipsFrame
type allocation = Frame.register Temp.Table.table

fun color {interference, initial, spillCost, registers} =
    (Temp.Table.empty, [])
end
