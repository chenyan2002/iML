(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML closure of value environments
 *
 * Definition, Section 4.7 and 4.8
 *)

structure Clos : CLOS =
struct
    (* Import *)

    open GrammarCore
    open StaticObjectsCore


    (* Check whether a pattern binds an identifier *)

    fun ? bindsX(NONE,   vid) = false
      | ? bindsX(SOME x, vid) = bindsX(x, vid)

    fun bindsAtPat(WILDCARDAtPat(_), vid)   = false
      | bindsAtPat(SCONAtPat(_, scon), vid) = false
      | bindsAtPat(IDAtPat(_, _, longvid), vid) =
	let
	    val (strids,vid') = LongVId.explode longvid
	in
	    List.null strids andalso vid = vid'
	end
      | bindsAtPat(RECORDAtPat(_, patrow_opt), vid) =
	    ?bindsPatRow(patrow_opt, vid)
      | bindsAtPat(PARAtPat(_, pat), vid) = bindsPat(pat, vid)

    and bindsPatRow(DOTSPatRow(_), vid) = false
      | bindsPatRow(FIELDPatRow(_, lab, pat, patrow_opt), vid) =
	    bindsPat(pat, vid) orelse ?bindsPatRow(patrow_opt, vid)

    and bindsPat(ATPat(_, atpat), vid)              = bindsAtPat(atpat, vid)
      | bindsPat(CONPat(_, _, longvid, atpat), vid) = bindsAtPat(atpat, vid)
      | bindsPat(COLONPat(_, pat, ty), vid)         = bindsPat(pat, vid)
      | bindsPat(ASPat(_, _, vid', ty_opt, pat), vid) =
	    vid = vid' orelse bindsPat(pat, vid)


    (* Non-expansive expressions [Section 4.7] *)

    fun ? isNonExpansiveX C  NONE    = true
      | ? isNonExpansiveX C (SOME x) = isNonExpansiveX C x

    fun isNonExpansiveAtExp C (SCONAtExp(_, scon))         = true
      | isNonExpansiveAtExp C (IDAtExp(_, _, longvid))     = true
      | isNonExpansiveAtExp C (RECORDAtExp(_, exprow_opt)) =
	    ?isNonExpansiveExpRow C exprow_opt
      | isNonExpansiveAtExp C (PARAtExp(_, exp)) = isNonExpansiveExp C exp
      | isNonExpansiveAtExp C  _                 = false

    and isNonExpansiveExpRow C (ExpRow(_, lab, exp, exprow_opt)) =
	    isNonExpansiveExp C exp andalso ?isNonExpansiveExpRow C exprow_opt

    and isNonExpansiveExp C (ATExp(_, atexp)) = isNonExpansiveAtExp C atexp
      | isNonExpansiveExp C (APPExp(_, exp, atexp)) =
	    isConExp C exp andalso isNonExpansiveAtExp C atexp
      | isNonExpansiveExp C (COLONExp(_, exp, ty))  = isNonExpansiveExp C exp
      | isNonExpansiveExp C (FNExp(_, match))       = true
      | isNonExpansiveExp C  _                      = false

    and isConAtExp C (PARAtExp(_, exp))       = isConExp C exp
      | isConAtExp C (IDAtExp(_, _, longvid)) =
	    LongVId.explode longvid <> ([],VId.fromString "ref") andalso
	    (case Context.findLongVId(C, longvid)
	       of SOME(_,is,_) => is = IdStatus.c orelse is = IdStatus.e
		| NONE       => false
	    )
      | isConAtExp C  _                            = false

    and isConExp C (ATExp(_, atexp))                  = isConAtExp C atexp
      | isConExp C (COLONExp(_, ATExp(_, atexp), ty)) = isConAtExp C atexp
      | isConExp C  _                                 = false


    (* Closure [Section 4.8] *)

    fun hasNonExpansiveRHS C (vid, PLAINValBind(I, pat, exp, valbind_opt)) =
	if bindsPat(pat, vid) then
	    isNonExpansiveExp C exp
	else
	    hasNonExpansiveRHS C (vid, valOf valbind_opt)

      | hasNonExpansiveRHS C (vid, RECValBind _) =
	    (* A rec valbind can only contain functions. *)
	    true

    fun Clos (C,valbind) VE =
	let
	    val tyvarsC = Context.tyvars C
	    val undetsC = Context.undetermined C

	    fun ClosType vid tau =
		if hasNonExpansiveRHS C (vid, valbind) then
		    let
			val tyvars =
			    TyVarSet.difference(Type.tyvars tau, tyvarsC)
			val undets =
			    StampMap.difference(Type.undetermined tau, undetsC)
			val tyvars' = StampMap.map TyVar.invent undets
			val det     = StampMap.map Type.fromTyVar tyvars'
		    in
			(TyVarSet.listItems tyvars @ StampMap.listItems tyvars',
			 Type.determine det tau)
		    end
		else
		    ( [], tau )
	in
	    VIdMap.mapi (fn(vid, ((_,tau),is, info)) => (ClosType vid tau, is, info)) VE
	end
end;
