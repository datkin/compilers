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
datatype level = Top | Nested of {parent: level, frame: Frame.frame}
type access = level * Frame.access

val outermost = Top

fun newLevel {parent, name, formals} =
    Nested {parent=parent, frame=Frame.newFrame {name=name, formals=true :: formals}}

fun formals (level as (Nested {parent, frame})) =
    (case Frame.formals frame of
       [] => (ErrorMsg.impossible "Frame has no static link"; [])
     | _ :: formals => map (fn frameAccess => (level, frameAccess)) formals)
  | formals Top = []

fun allocLocal (level as Nested {parent, frame}) escapes = (level, Frame.allocLocal frame escapes)
  | allocLocal Top _ = (ErrorMsg.impossible "Attempted to allocate in the outermost frame.";
                      raise Fail "Attempted to allocate in the outermost frame.")

end
