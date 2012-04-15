(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML syntactic restrictions for programs
 *)

structure SyntacticRestrictionsProgram : SYNTACTIC_RESTRICTIONS_PROGRAM =
struct
    (* Import *)

    open GrammarProgram

    type Basis = SyntacticRestrictionsModule.Basis


    (* Operation *)

    fun checkProgram(B, Program(I, topdec, program_opt)) =
	let
	    val (B1, topdec)  = SyntacticRestrictionsModule.checkTopDec(B, topdec)
	    val B'  = BindingBasis.plus(B, B1)
	    val (B'', program_opt) = case program_opt
			              of NONE         => (B', NONE)
			               | SOME program => let val (b,p) = checkProgram(B', program)
                                                        in (b, SOME p) end
	in
	    (B'', Program(I, topdec, program_opt))
	end
end;
