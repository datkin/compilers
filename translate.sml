signature TRANSLATE =
sig
  type exp
  type level
  type access

  val outermost : level
  val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
  val formals : level -> access list
  val allocLocal : level -> bool -> access
end

structure Translate : TRANSLATE =
struct
type exp = unit
type level = {depth: int, frame: Frame.frame}
type access = level * Frame.access

val outermost = {depth=0, frame=Frame.newFrame {name=Temp.newLabel (), formals=[]}}

fun newLevel {parent={depth, frame}, name, formals} =
    {depth=depth+1, frame=Frame.newFrame {name=name, formals=true :: formals}}

fun formals (level as {depth, frame}) =
    case Frame.formals frame of
      [] => (ErrorMsg.impossible "Frame has no static link"; [])
    | _ :: formals => map (fn frameAccess => (level, frameAccess)) formals

fun allocLocal (level as {depth, frame}) escapes = (level, Frame.allocLocal frame escapes)
end
