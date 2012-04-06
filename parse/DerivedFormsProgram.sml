(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML program derived forms
 *
 * Definition, Appendix A
 *)

structure DerivedFormsProgram :> DERIVED_FORMS_PROGRAM =
struct
    (* Import *)

    structure C  = GrammarCore
    structure M  = GrammarModule
    structure P  = GrammarProgram

    type Info    = GrammarProgram.Info

    type Exp     = GrammarCore.Exp
    type TopDec  = GrammarModule.TopDec
    type Program = GrammarProgram.Program


    (* Programs [Figure 18] *)

    fun TOPDECProgram(I, topdec, program_opt) =
	    P.Program(I, topdec, program_opt)

    fun EXPProgram(I, exp, program_opt) =
	let
	    val longvid = LongVId.fromId(VId.fromString "it")
	    val pat     = C.ATPat(I, C.IDAtPat(I, C.SANSOp, longvid))
	    val valbind = C.PLAINValBind(I, pat, exp, NONE)
	    val dec     = C.VALDec(I, C.TyVarseq(I, []), valbind)
	    val topdec  = M.STRDECTopDec(I, M.DECStrDec(I, dec), NONE)
	in
	    P.Program(I, topdec, program_opt)
	end
end;
