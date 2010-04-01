signature FRAME =
sig
  type frame
  type access
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
  val newFrame : {name: Temp.label, formals: bool list} -> frame
  val name : frame -> Temp.label
  val formals : frame -> access list
  val allocLocal : frame -> bool -> access
  val externalCall : string * Tree.exp list -> Tree.exp
  val procEntryExit1 : frame * Tree.stm -> Tree.stm

  val FP : Temp.temp
  val RV : Temp.temp
  val wordSize : int
  val exp : access -> Tree.exp -> Tree.exp

  val rewriteCall : Tree.exp * Tree.exp list -> Tree.exp
  val rewriteBody : Tree.stm * frame -> Tree.stm
  val SP : Temp.temp
  val RA : Temp.temp
end
