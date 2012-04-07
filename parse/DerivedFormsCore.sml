(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core derived forms
 *
 * Definition, Section 2.7 and Appendix A
 *
 * Notes:
 * - Two phrases named Fmatch and Fmrule have been added to factorize FvalBind.
 * - In Fvalbinds we do not enforce that all optional type annotations are
 *   syntactically identical (as the Definition enforces, although this seems
 *   to be a mistake).
 * - The Definition is somewhat inaccurate about the derived forms of Exp
 *   [Definition, Appendix A, Figure 15] in that most forms are actually AtExp
 *   derived forms, as can be seen from the full grammar [Definition,
 *   Appendix B, Figure 20]. To achieve consistency, the equivalent forms must
 *   be put in parentheses in some cases.
 * - The same goes for pattern derived forms [Definition, Appendix A, Figure 16;
 *   Appendix B, Figure 22].
 *)

structure DerivedFormsCore :> DERIVED_FORMS_CORE =
struct
    (* Import *)

    structure C    = GrammarCore

    type Info      = C.Info

    type Lab       = C.Lab
    type VId       = C.VId

    type Op        = C.Op
    type AtExp     = C.AtExp
    type AppExp    = C.AtExp list
    type InfExp    = C.Exp
    type Exp       = C.Exp
    type Match     = C.Match
    type Mrule     = C.Mrule
    type Dec       = C.Dec
    type ValBind   = C.ValBind
    type FvalBind  = C.ValBind
    type Fmatch    = C.Match * C.VId * int
    type Fmrule    = C.Mrule * C.VId * int
    type TypBind   = C.TypBind
    type DatBind   = C.DatBind
    type AtPat     = C.AtPat
    type PatRow    = C.PatRow
    type Pat       = C.Pat
    type Ty        = C.Ty
    type TyVarseq  = C.TyVarseq


    (* Some helpers *)

    val vidFALSE               = VId.fromString "false"
    val vidTRUE                = VId.fromString "true"
    val vidNIL                 = VId.fromString "nil"
    val vidCONS                = VId.fromString "::"
    val longvidCONS            = LongVId.fromId vidCONS

    fun LONGVIDExp(I, longvid) = C.ATExp(I, C.IDAtExp(I, C.SANSOp, longvid))
    fun LONGVIDPat(I, longvid) = C.ATPat(I, C.IDAtPat(I, C.SANSOp, longvid))

    fun VIDAtExp(I, vid)       = C.IDAtExp(I, C.SANSOp, LongVId.fromId vid)
    fun VIDAtPat(I, vid)       = C.IDAtPat(I, C.SANSOp, LongVId.fromId vid)
    fun VIDExp(I, vid)         = LONGVIDExp(I, LongVId.fromId vid)
    fun VIDPat(I, vid)         = LONGVIDPat(I, LongVId.fromId vid)

    fun FALSEExp(I)            = VIDExp(I, vidFALSE)
    fun TRUEExp(I)             = VIDExp(I, vidTRUE)
    fun NILAtExp(I)            = VIDAtExp(I, vidNIL)
    fun CONSExp(I)             = VIDExp(I, vidCONS)

    fun FALSEPat(I)            = VIDPat(I, vidFALSE)
    fun TRUEPat(I)             = VIDPat(I, vidTRUE)
    fun NILAtPat(I)            = VIDAtPat(I, vidNIL)


    (* Rewriting of withtype declarations [Appendix A, 2nd bullet] *)
    (* TODO: replaceLv and rewriteLv  *)

    fun findTyCon(tycon, C.TypBind(_, tyvarseq, tycon', ty, typbind_opt)) =
	    if tycon' = tycon then
		SOME(tyvarseq, ty)
	    else
		Option.mapPartial (fn typbind => findTyCon(tycon, typbind))
				  typbind_opt


    fun replaceTy (C.TyVarseq(_,tyvars), C.Tyseq(I',tys)) (C.VARTy(I,tyvar)) =
	let
	    fun loop(tyvar'::tyvars', ty'::tys') =
		    if tyvar' = tyvar then
			ty'
		    else
			loop(tyvars', tys')
	      | loop([],_) =
		    Error.error(I, "unbound type variable")
	      | loop(_,[]) =
		    Error.error(I', "type sequence has wrong arity")
	in
	    loop(tyvars, tys)
	end

      | replaceTy tyvarseq_tyseq (C.RECORDTy(I, tyrow_opt, level)) =
	    C.RECORDTy(I, Option.map (replaceTyRow tyvarseq_tyseq) tyrow_opt, level)

      | replaceTy tyvarseq_tyseq (C.CONTy(I, tyseq', tycon, level)) =
	    C.CONTy(I, replaceTyseq tyvarseq_tyseq tyseq', tycon, level)

      | replaceTy tyvarseq_tyseq (C.ARROWTy(I, ty1, ty2, mode, level)) =
	    C.ARROWTy(I, replaceTy tyvarseq_tyseq ty1,
			 replaceTy tyvarseq_tyseq ty2,
                         mode, level)

      | replaceTy tyvarseq_tyseq (C.PARTy(I, ty)) =
	    C.PARTy(I, replaceTy tyvarseq_tyseq ty)

    and replaceTyRow tyvarseq_tyseq (C.TyRow(I, lab, ty, tyrow_opt)) =
	    C.TyRow(I, lab, replaceTy tyvarseq_tyseq ty, 
		       Option.map (replaceTyRow tyvarseq_tyseq) tyrow_opt)

    and replaceTyseq tyvarseq_tyseq (C.Tyseq(I, tys)) =	  
	    C.Tyseq(I, List.map (replaceTy tyvarseq_tyseq) tys)


    fun rewriteTy typbind (ty as C.VARTy _) = ty

      | rewriteTy typbind (C.RECORDTy(I, tyrow_opt, level)) =
	    C.RECORDTy(I, Option.map (rewriteTyRow typbind) tyrow_opt, level)

      | rewriteTy typbind (C.CONTy(I, tyseq, longtycon, level)) =
	let 
	    val tyseq'          = rewriteTyseq typbind tyseq
	    val (strids, tycon) = LongTyCon.explode longtycon
	in
	    if not(List.null strids) then
		C.CONTy(I, tyseq', longtycon, level)
	    else
		case findTyCon(tycon, typbind)
		  of SOME(tyvarseq', ty') => replaceTy (tyvarseq',tyseq') ty'
		   | NONE                 => C.CONTy(I, tyseq', longtycon, level)
	end

      | rewriteTy typbind (C.ARROWTy(I, ty1, ty2, mode, level)) =
	    C.ARROWTy(I, rewriteTy typbind ty1, rewriteTy typbind ty2, mode, level)

      | rewriteTy typbind (C.PARTy(I, ty)) =
	    C.PARTy(I, rewriteTy typbind ty)

    and rewriteTyRow typbind (C.TyRow(I, lab, ty, tyrow_opt)) =
	    C.TyRow(I, lab, rewriteTy typbind ty,
		       Option.map (rewriteTyRow typbind) tyrow_opt)

    and rewriteTyseq typbind (C.Tyseq(I, tys)) =
	    C.Tyseq(I, List.map (rewriteTy typbind) tys)

    fun rewriteConBind typbind (C.ConBind(I, op_opt, vid, ty_opt, conbind_opt))=
	    C.ConBind(I, op_opt, vid,
			 Option.map (rewriteTy typbind) ty_opt,
			 Option.map (rewriteConBind typbind) conbind_opt)

    fun rewriteDatBind typbind (C.DatBind(I, tyvarseq, tycon, conbind,
							      datbind_opt)) =
	case findTyCon(tycon, typbind)
	  of NONE =>
	     C.DatBind(I, tyvarseq, tycon, rewriteConBind typbind conbind,
			  Option.map (rewriteDatBind typbind) datbind_opt)
	   | SOME _ =>
		Error.error(I, "duplicate type constructor \
			       \in recursive type declaration")


    (* Patterns [Figure 16] *)

    fun UNITAtPat(I) = C.RECORDAtPat(I, NONE)

    fun TUPLEAtPat(I, [pat]) = C.PARAtPat(I, pat)
      | TUPLEAtPat(I,  pats) =
	let
	    fun toPatRow(n,    []     ) = NONE
	      | toPatRow(n, pat::pats') =
		SOME(C.FIELDPatRow(I, Lab.fromInt n, pat, toPatRow(n+1,pats')))
	in
	    C.RECORDAtPat(I, toPatRow(1, pats))
	end

    fun LISTAtPat(I, [])   = NILAtPat(I)
      | LISTAtPat(I, pats) = 
	let
	    fun toPatList    []       = C.ATPat(I, NILAtPat(I))
	      | toPatList(pat::pats') =
		C.CONPat(I, C.SANSOp, longvidCONS,
			    TUPLEAtPat(I, [pat, toPatList pats']))
	in
	    C.PARAtPat(I, toPatList pats)
	end


    (* Pattern Rows [Figure 16] *)

    fun IDPatRow(I, vid, ty_opt, pat_opt, patrow_opt) =
	let
	    val lab    = Lab.fromString(VId.toString vid)
	    val vidPat = VIDPat(I, vid)
	    val pat    =
		case (ty_opt, pat_opt)
		  of (NONE,    NONE) => vidPat
		   | (SOME ty, NONE) => C.COLONPat(I, vidPat, ty)
		   | ( _ , SOME pat) => C.ASPat(I, C.SANSOp,vid,ty_opt,pat)
	in
	    C.FIELDPatRow(I, lab, pat, patrow_opt)
	end


    (* Expressions [Figure 15] *)

    fun UNITAtExp(I) = C.RECORDAtExp(I, NONE)

    fun TUPLEAtExp(I, [exp]) = C.PARAtExp(I, exp)
      | TUPLEAtExp(I,  exps) =
	let
	    fun toExpRow(n,    []     ) = NONE
	      | toExpRow(n, exp::exps') =
		SOME(C.ExpRow(I, Lab.fromInt n, exp, toExpRow(n+1, exps')))
	in
	    C.RECORDAtExp(I, toExpRow(1, exps))
	end

    fun HASHAtExp(I, lab) =
	let
	    val vid    = VId.invent()
	    val dots   = C.DOTSPatRow(I)
	    val patrow = C.FIELDPatRow(I, lab, VIDPat(I, vid), SOME dots)
	    val pat    = C.ATPat(I, C.RECORDAtPat(I, SOME patrow))
	    val mrule  = C.Mrule(I, pat, VIDExp(I, vid))
	    val match  = C.Match(I, mrule, NONE)
	in
	    C.PARAtExp(I, C.FNExp(I, match))
	end

    fun CASEExp(I, exp, match) =
	let
	    val function = C.ATExp(I, C.PARAtExp(I, C.FNExp(I, match)))
	in
	    C.APPExp(I, function, C.PARAtExp(I, exp))
	end

    fun IFExp(I, exp1, exp2, exp3) =
	let
	    val mruleTrue  = C.Mrule(I, TRUEPat(I), exp2)
	    val mruleFalse = C.Mrule(I, FALSEPat(I), exp3)
	    val matchFalse = C.Match(I, mruleFalse, NONE)
	    val matchTrue  = C.Match(I, mruleTrue, SOME matchFalse)
	in
	    CASEExp(I, exp1, matchTrue)
	end

    fun ORELSEExp (I, exp1, exp2) = IFExp(I, exp1, TRUEExp(I), exp2)

    fun ANDALSOExp(I, exp1, exp2) = IFExp(I, exp1, exp2, FALSEExp(I))

    fun SEQAtExp(I, exps) =
	let
	    val wildcard             = C.ATPat(I, C.WILDCARDAtPat(I))

	    fun toExpSeq []          = raise Fail "DerivedFormsCore.SEQAtExp: \
						  \empty exp list"
	      | toExpSeq [exp]       = exp
	      | toExpSeq(exp::exps') =
		  let
		      val mrule = C.Mrule(I, wildcard, toExpSeq exps')
		      val match = C.Match(I, mrule, NONE)
		  in
		      CASEExp(I, exp, match)
		  end
	in
	    C.PARAtExp(I, toExpSeq exps)
	end

    fun LETAtExp(I, dec, [exp]) = C.LETAtExp(I, dec, exp)
      | LETAtExp(I, dec,  exps) =
	    C.LETAtExp(I, dec, C.ATExp(I, SEQAtExp(I, exps)))

    fun WHILEExp(I, exp1, exp2) =
	let
	    val vid       = VId.invent()
	    val vidExp    = VIDExp(I, vid)
	    val unitAtExp = UNITAtExp(I)
	    val unitExp   = C.ATExp(I, unitAtExp)
	    val callVid   = C.APPExp(I, vidExp, unitAtExp)

	    val seqExp    = C.ATExp(I, SEQAtExp(I, [exp2, callVid]))
	    val fnBody    = IFExp(I, exp1, seqExp, unitExp)
	    val mrule     = C.Mrule(I, C.ATPat(I, UNITAtPat(I)), fnBody)
	    val match     = C.Match(I, mrule, NONE)
	    val fnExp     = C.FNExp(I, match)
	    val fnBind    = C.PLAINValBind(I, VIDPat(I, vid), fnExp, NONE)
	    val valbind   = C.RECValBind(I, fnBind)
	    val dec       = C.VALDec(I, C.TyVarseq(I, []), valbind)
	in
	    C.ATExp(I, C.LETAtExp(I, dec, callVid))
	end

    fun LISTAtExp(I, [])   = NILAtExp(I)
      | LISTAtExp(I, exps) =
	let
	    fun toExpList    []       = C.ATExp(I, NILAtExp(I))
	      | toExpList(exp::exps') =
		C.APPExp(I, CONSExp(I), TUPLEAtExp(I, [exp, toExpList exps']))
	in
	    C.PARAtExp(I, toExpList exps)
	end


    (* Type Expressions [Figure 16] *)

    fun TUPLETy(I, [ty], level) = ty
      | TUPLETy(I,  tys, level) =
	let
	    fun toTyRow(n,   []    ) = NONE
	      | toTyRow(n, ty::tys') =
		SOME(C.TyRow(I, Lab.fromInt n, ty, toTyRow(n+1, tys')))
	in
	    C.RECORDTy(I, toTyRow(1, tys), level)
	end


    (* Function-value Bindings [Figure 17] *)

    fun FvalBind(I, (match, vid, arity), fvalbind_opt) =
	let
	    fun abstract(0, vidExps) =
		let
		    val exp = C.ATExp(I, TUPLEAtExp(I, List.rev vidExps))
		in
		    CASEExp(I, exp, match)
		end

	      | abstract(n, vidExps) =
		let
		    val vid   = VId.invent()
		    val exp   = VIDExp(I, vid)
		    val pat   = VIDPat(I, vid)
		    val mrule = C.Mrule(I, pat, abstract(n-1, exp::vidExps))
		in
		    C.FNExp(I, C.Match(I, mrule, NONE))
		end

	    val exp = abstract(arity, [])
	    val pat = VIDPat(I, vid)
	in
	    C.PLAINValBind(I, pat, exp, fvalbind_opt)
	end


    fun Fmatch(I, (mrule, vid, arity), NONE) =
	    ( C.Match(I, mrule, NONE), vid, arity )

      | Fmatch(I, (mrule, vid, arity), SOME(match, vid', arity')) =
	    if vid <> vid' then
		Error.error(I, "inconsistent function identifier")
	    else if arity <> arity' then
		Error.error(I, "inconsistent function arity")
	    else
		( C.Match(I, mrule, SOME match), vid, arity )


    fun Fmrule(I, _, vid, atpats, ty_opt, exp) =
	let
	    val pats = List.map (fn atpat => C.ATPat(I, atpat)) atpats
	    val pat' = C.ATPat(I, TUPLEAtPat(I, pats))
	    val exp' = case ty_opt
			 of NONE    => exp
			  | SOME ty => C.COLONExp(I, exp, ty)
	    val arity = List.length atpats
	in
	    ( C.Mrule(I, pat', exp'), vid, arity )
	end


    (* Declarations [Figure 17] *)

    fun FUNDec(I, tyvarseq, fvalbind) =
	    C.VALDec(I, tyvarseq, C.RECValBind(I, fvalbind))

    fun DATATYPEDec(I, datbind, NONE)         = C.DATATYPEDec(I, datbind)
      | DATATYPEDec(I, datbind, SOME typbind) =
	let
	    val datbind' = rewriteDatBind typbind datbind
	in
	    C.SEQDec(I, C.DATATYPEDec(C.infoDatBind datbind, datbind'),
			C.TYPEDec(C.infoTypBind typbind, typbind))
	end

    fun ABSTYPEDec(I, datbind, NONE, dec)         = C.ABSTYPEDec(I, datbind,dec)
      | ABSTYPEDec(I, datbind, SOME typbind, dec) =
	let
	    val I'       = C.infoTypBind typbind
	    val datbind' = rewriteDatBind typbind datbind
	in
	    C.ABSTYPEDec(I, datbind', C.SEQDec(I, C.TYPEDec(I', typbind), dec))
	end
end;
