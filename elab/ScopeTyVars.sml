(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML scope of type variables
 *
 * Definition, Section 4.6
 *)

structure ScopeTyVars : SCOPE_TYVARS =
struct
    (* Import *)

    open GrammarCore
    type TyVarSet = TyVarSet.set


    (* Helpers *)

    val op+ = TyVarSet.union

    fun ? tyvarsX  NONE    = TyVarSet.empty
      | ? tyvarsX (SOME x) = tyvarsX x


    (* Operation *)

    fun unguardedTyVarsAtExp(SCONAtExp(_, _)) =
	    TyVarSet.empty
      | unguardedTyVarsAtExp(IDAtExp(_, _, _)) =
	    TyVarSet.empty
      | unguardedTyVarsAtExp(RECORDAtExp(_, exprow_opt)) =
	    ?unguardedTyVarsExpRow exprow_opt
      | unguardedTyVarsAtExp(LETAtExp(_, dec, exp)) =
	    unguardedTyVarsDec dec + unguardedTyVarsExp exp
      | unguardedTyVarsAtExp(PARAtExp(_, exp)) =
	    unguardedTyVarsExp exp

    and unguardedTyVarsExpRow(ExpRow(_, lab, exp, exprow_opt)) =
	    unguardedTyVarsExp exp + ?unguardedTyVarsExpRow exprow_opt

    and unguardedTyVarsExp(ATExp(_, atexp)) =
	    unguardedTyVarsAtExp atexp
      | unguardedTyVarsExp(APPExp(_, exp, atexp)) =
	    unguardedTyVarsExp exp + unguardedTyVarsAtExp atexp
      | unguardedTyVarsExp(COLONExp(_, exp, ty)) =
	    unguardedTyVarsExp exp + unguardedTyVarsTy ty
      | unguardedTyVarsExp(HANDLEExp(_, exp, match)) =
	    unguardedTyVarsExp exp + unguardedTyVarsMatch match
      | unguardedTyVarsExp(RAISEExp(_, exp)) =
	    unguardedTyVarsExp exp
      | unguardedTyVarsExp(FNExp(_, match)) =
	    unguardedTyVarsMatch match

    and unguardedTyVarsMatch(Match(_, mrule, match_opt)) =
	    unguardedTyVarsMrule mrule + ?unguardedTyVarsMatch match_opt

    and unguardedTyVarsMrule(Mrule(_, pat, exp)) =
	    unguardedTyVarsPat pat + unguardedTyVarsExp exp

    and unguardedTyVarsDec(VALDec(_, _, _)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(TYPEDec(_, _)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(DATATYPEDec(_, _)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(DATATYPE2Dec(_, _, _)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(ABSTYPEDec(_, datbind, dec)) =
	    unguardedTyVarsDec dec
      | unguardedTyVarsDec(EXCEPTIONDec(_, exbind)) =
	    unguardedTyVarsExBind exbind
      | unguardedTyVarsDec(LOCALDec(_, dec1, dec2)) =
	    unguardedTyVarsDec dec1 + unguardedTyVarsDec dec2
      | unguardedTyVarsDec(OPENDec(_, _)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(EMPTYDec(_)) =
	    TyVarSet.empty
      | unguardedTyVarsDec(SEQDec(_, dec1, dec2)) =
	    unguardedTyVarsDec dec1 + unguardedTyVarsDec dec2

    and unguardedTyVarsValBind(PLAINValBind(_, pat, exp, valbind_opt)) =
	    unguardedTyVarsPat pat + unguardedTyVarsExp exp +
	    ?unguardedTyVarsValBind valbind_opt
      | unguardedTyVarsValBind(RECValBind(_, valbind)) =
	    unguardedTyVarsValBind valbind

    and unguardedTyVarsExBind(NEWExBind(_, _, vid, ty_opt, exbind_opt)) =
	    ?unguardedTyVarsTy ty_opt + ?unguardedTyVarsExBind exbind_opt
      | unguardedTyVarsExBind(EQUALExBind(_, _, vid, _, longvid, exbind_opt)) =
	    ?unguardedTyVarsExBind exbind_opt

    and unguardedTyVarsAtPat(WILDCARDAtPat(_)) =
	    TyVarSet.empty
      | unguardedTyVarsAtPat(SCONAtPat(_, _)) =
	    TyVarSet.empty
      | unguardedTyVarsAtPat(IDAtPat(_, _, _)) =
	    TyVarSet.empty
      | unguardedTyVarsAtPat(RECORDAtPat(_, patrow_opt)) =
	    ?unguardedTyVarsPatRow patrow_opt
      | unguardedTyVarsAtPat(PARAtPat(_, pat)) =
	    unguardedTyVarsPat pat

    and unguardedTyVarsPatRow(DOTSPatRow(_)) = TyVarSet.empty
      | unguardedTyVarsPatRow(FIELDPatRow(_, lab, pat, patrow_opt)) =
	    unguardedTyVarsPat pat + ?unguardedTyVarsPatRow patrow_opt

    and unguardedTyVarsPat(ATPat(_, atpat)) =
	    unguardedTyVarsAtPat atpat
      | unguardedTyVarsPat(CONPat(_, _, longvid, atpat)) =
	    unguardedTyVarsAtPat atpat
      | unguardedTyVarsPat(COLONPat(_, pat, ty)) =
	    unguardedTyVarsPat pat + unguardedTyVarsTy ty
      | unguardedTyVarsPat(ASPat(_, _, vid, ty_opt, pat)) =
	    ?unguardedTyVarsTy ty_opt + unguardedTyVarsPat pat

    and unguardedTyVarsTy(VARTy(_, tyvar)) = TyVarSet.singleton tyvar
      | unguardedTyVarsTy(RECORDTy(_, tyrow_opt,_)) =
	    ?unguardedTyVarsTyRow tyrow_opt
      | unguardedTyVarsTy(CONTy(_, tyseq, longtycon,_)) =
	    unguardedTyVarsTyseq tyseq
      | unguardedTyVarsTy(ARROWTy(_, ty, ty',_,_)) =
	    unguardedTyVarsTy ty + unguardedTyVarsTy ty'
      | unguardedTyVarsTy(PARTy(_, ty)) =
	    unguardedTyVarsTy ty

    and unguardedTyVarsTyRow(TyRow(_, lab, ty, tyrow_opt)) =
	    unguardedTyVarsTy ty + ?unguardedTyVarsTyRow tyrow_opt

    and unguardedTyVarsTyseq(Tyseq(_, tys)) =
	    List.foldl (fn(ty,U) => unguardedTyVarsTy ty + U) TyVarSet.empty tys


    (* Export *)

    val unguardedTyVars = unguardedTyVarsValBind
end;
