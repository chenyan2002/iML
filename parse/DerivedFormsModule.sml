(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML modules derived forms
 *
 * Definition, Appendix A
 *
 * Notes:
 * - A phrase named SynDesc has been added to factorize type synonym
 *   specifications.
 * - Similarly, a phrase named TyReaDesc has been added to factorize type
 *   realisation signature expressions.
 * - The structure sharing derived form is missing since it cannot be resolved
 *   syntactically. It has been moved to the bare grammar.
 *)

structure DerivedFormsModule :> DERIVED_FORMS_MODULE =
struct
    (* Import *)

    structure C     = GrammarCore
    structure M     = GrammarModule

    type Info       = M.Info

    type VId        = M.VId
    type TyCon      = M.TyCon
    type StrId      = M.StrId
    type SigId      = M.SigId
    type FunId      = M.FunId
    type longTyCon  = M.longTyCon

    type Ty         = M.Ty
    type TyVarseq   = M.TyVarseq

    type StrExp     = M.StrExp
    type StrDec     = M.StrDec
    type StrBind    = M.StrBind
    type SigExp     = M.SigExp
    type TyReaDesc  = (M.Info * M.TyVarseq * M.longTyCon * M.Ty) list
    type Spec       = M.Spec
    type SynDesc    = (M.Info * M.TyVarseq * M.TyCon * M.Ty) list
    type FunBind    = M.FunBind


    (* Structure Bindings [Figure 18] *)

    fun TRANSStrBind(I, strid, NONE, strexp, strbind_opt) =
	    M.StrBind(I, strid, strexp, strbind_opt)

      | TRANSStrBind(I, strid, SOME sigexp, strexp, strbind_opt) =
	    M.StrBind(I, strid, M.COLONStrExp(I, strexp, sigexp), strbind_opt)

    fun SEALStrBind(I, strid, sigexp, strexp, strbind_opt) =
	    M.StrBind(I, strid, M.SEALStrExp(I, strexp, sigexp), strbind_opt)


    (* Structure Expressions [Figure 18] *)

    fun APPDECStrExp(I, funid, strdec) =
	    M.APPStrExp(I, funid, M.STRUCTStrExp(M.infoStrDec strdec, strdec))


    (* Functor Bindings [Figure 18] *)

    fun TRANSFunBind(I, funid, strid, sigexp, NONE, strexp, funbind_opt) =
	    M.FunBind(I, funid, strid, sigexp, strexp, funbind_opt)

      | TRANSFunBind(I, funid, strid,sigexp, SOME sigexp', strexp, funbind_opt)=
	    M.FunBind(I, funid, strid, sigexp, M.COLONStrExp(I, strexp,sigexp'),
			 funbind_opt)

    fun SEALFunBind(I, funid, strid, sigexp, sigexp', strexp, funbind_opt) =
	    M.FunBind(I, funid, strid, sigexp, M.SEALStrExp(I, strexp, sigexp'),
			 funbind_opt)


    fun TRANSSPECFunBind(I, funid, spec, sigexp_opt, strexp, funbind_opt) =
	let
	    val I'     = M.infoStrExp strexp
	    val strid  = StrId.invent()
	    val sigexp = M.SIGSigExp(M.infoSpec spec, spec)

	    val strdec = M.DECStrDec(I', C.OPENDec(I',[LongStrId.fromId strid]))
	    val strexp'= case sigexp_opt
			   of NONE         => strexp
			    | SOME sigexp' => M.COLONStrExp(I', strexp, sigexp')
	    val letexp = M.LETStrExp(I', strdec, strexp')
	in
	    M.FunBind(I, funid, strid, sigexp, letexp, funbind_opt)
	end

    fun SEALSPECFunBind(I, funid, spec, sigexp', strexp, funbind_opt) =
	let
	    val I'     = M.infoStrExp strexp
	    val strid  = StrId.invent()
	    val sigexp = M.SIGSigExp(M.infoSpec spec, spec)

	    val strdec = M.DECStrDec(I', C.OPENDec(I',[LongStrId.fromId strid]))
	    val strexp'= M.COLONStrExp(I', strexp, sigexp')
	    val letexp = M.LETStrExp(I', strdec, strexp')
	in
	    M.FunBind(I, funid, strid, sigexp, letexp, funbind_opt)
	end


    (* Specifications [Figure 19] *)

    fun SYNSpec(I, [])                            = M.EMPTYSpec(I)
      | SYNSpec(I, (I',tyvarseq,tycon,ty)::syns') =
	let
	    val longtycon = LongTyCon.fromId tycon
	    val typdesc = M.TypDesc(I', tyvarseq, tycon, NONE)
	    val sigexp  = M.SIGSigExp(I', M.TYPESpec(I', typdesc))
	    val sigexp' = M.WHERETYPESigExp(I', sigexp, tyvarseq, longtycon, ty)
	    val spec1   = M.INCLUDESpec(I', sigexp')
	in
	    M.SEQSpec(I, spec1, SYNSpec(I, syns'))
	end

    fun INCLUDEMULTISpec(I,      []       ) = M.EMPTYSpec(I)
      | INCLUDEMULTISpec(I, sigid::sigids') =
	let
	    val spec1 = M.INCLUDESpec(I, M.IDSigExp(I, sigid))
	in
	    M.SEQSpec(I, spec1, INCLUDEMULTISpec(I, sigids'))
	end


    fun SynDesc(I, tyvarseq, tycon, ty, NONE) =
	    (I, tyvarseq, tycon, ty) :: []

      | SynDesc(I, tyvarseq, tycon, ty, SOME syndesc) =
	    (I, tyvarseq, tycon, ty) :: syndesc


    (* Signature Expressions [Figure 19] *)

    fun WHERETYPESigExp(I, sigexp,                           []     ) = sigexp
      | WHERETYPESigExp(I, sigexp, (I',tyvarseq,longtycon,ty)::reas') =
	let
	    val sigexp' = M.WHERETYPESigExp(I', sigexp, tyvarseq, longtycon, ty)
	in
	    WHERETYPESigExp(I, sigexp', reas')
	end


    fun TyReaDesc(I, tyvarseq, longtycon, ty, NONE) =
	    (I, tyvarseq, longtycon, ty) :: []

      | TyReaDesc(I, tyvarseq, longtycon, ty, SOME tyreadesc) =
	    (I, tyvarseq, longtycon, ty) :: tyreadesc
end;
