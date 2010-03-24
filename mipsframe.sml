structure MipsFrame :> FRAME =
struct
  structure T = Tree

  val offset = ~4
  val maxRegisterArgs = 4
  val FP = Temp.newTemp ()
  val wordSize = 4

  datatype access = InFrame of int | InReg of Temp.temp
  type frame = {formals: access list, localCount: int ref,
                name: Temp.label, frameOffset: int ref}

  fun escapeToAccess (true, (access, frameOffset, registerArgs)) =
      (InFrame (frameOffset + offset) :: access, frameOffset + offset, registerArgs)
    | escapeToAccess (false, (access, frameOffset, registerArgs)) =
      if registerArgs < maxRegisterArgs then
        (InReg (Temp.newTemp ()) :: access, frameOffset, registerArgs + 1)
      else
        (InFrame (frameOffset + offset) :: access, frameOffset + offset, registerArgs)

  fun newFrame {name, formals} =
    let
      val (formals, frameOffset, _) = (foldl escapeToAccess ([], 0, 0) formals)
    in
      {name = name, formals = (rev formals),
       localCount = ref 0, frameOffset = ref frameOffset}
    end

  fun name (f: frame) = #name f
  fun formals (f: frame) = #formals f

  fun allocLocal (frame: frame) true =
        let
          val localCount = #localCount frame
          val frameOffset = #frameOffset frame
        in
          (localCount := !localCount + 1;
           frameOffset := !frameOffset + offset;
           InFrame (!frameOffset))
        end
    | allocLocal frame false =
        let
          val localCount = #localCount frame
        in
          (localCount := !localCount + 1;
           InReg (Temp.newTemp ()))
        end

  fun exp (InFrame offset) fpExp = T.MEM (T.BINOP (T.PLUS, T.CONST offset, fpExp))
    | exp (InReg temp) _         = T.TEMP temp

end

structure Frame : FRAME = MipsFrame
