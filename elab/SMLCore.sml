(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract core grammar
 *)

structure SMLCore : SML_CORE =
struct
    (* Import *)

    open GrammarCore
    open PPGrammar


    (* Special constants *)

    fun ppSCon(out, i, scon) =
	let
	    val tag = case scon of SCon.INT _    => "INT"
				 | SCon.WORD _   => "WORD"
				 | SCon.STRING _ => "STRING"
				 | SCon.CHAR _   => "CHAR"
				 | SCon.REAL _   => "REAL"
	in
	    ppAtom(out, i, tag ^ "SCon", SCon.toString scon)
	end


    (* Identifiers *)

    fun ppLab(out, i, lab)     = ppAtom(out, i, "Lab", Lab.toString lab)
    fun ppVId(out, i, vid)     = ppAtom(out, i, "VId", VId.toString vid)
    fun ppTyVar(out, i, tyvar) = ppAtom(out, i, "TyVar", TyVar.toString tyvar)
    fun ppTyCon(out, i, tycon) = ppAtom(out, i, "TyCon", TyCon.toString tycon)
    fun ppStrId(out, i, strid) = ppAtom(out, i, "StrId", StrId.toString strid)
    fun ppLvVar(out, i, lvvar) = ppAtom(out, i, "LvVar", LvVar.toString lvvar)

    fun ppLongVId(out, i, longvid) =
	    ppAtom(out, i, "LongVId", LongVId.toString longvid)
    fun ppLongTyCon(out, i, longtycon) =
	    ppAtom(out, i, "LongTyCon", LongTyCon.toString longtycon)
    fun ppLongStrId(out, i, longstrid) =
	    ppAtom(out, i, "LongStrId", LongStrId.toString longstrid)


    (* Expressions *)

    fun ppAtExp(out, i, SCONAtExp(I, scon)) =
	    ppElem(out, i, "SCONAtExp", I,
		   [sub ppSCon scon])
      | ppAtExp(out, i, IDAtExp(I, _, longvid)) =
	    ppElem(out, i, "IDAtExp", I,
		   [sub ppLongVId longvid])
      | ppAtExp(out, i, RECORDAtExp(I, exprow_opt)) =
	    ppElem(out, i, "RECORDAtExp", I,
		   [subo ppExpRow exprow_opt])
      | ppAtExp(out, i, LETAtExp(I, dec, exp)) =
	    ppElem(out, i, "LETAtExp", I,
		   [sub ppDec dec, sub ppExp exp])
      | ppAtExp(out, i, PARAtExp(I, exp)) =
	    ppElem(out, i, "PARAtExp", I,
		   [sub ppExp exp])

    and ppExpRow(out, i, ExpRow(I, lab, exp, exprow_opt)) =
	    ppElem(out, i, "ExpRow", I,
		   [sub ppLab lab, sub ppExp exp, subo ppExpRow exprow_opt])

    and ppExp(out, i, ATExp(I, atexp)) =
	    ppElem(out, i, "ATExp", I,
		   [sub ppAtExp atexp])
      | ppExp(out, i, APPExp(I, exp, atexp)) =
	    ppElem(out, i, "APPExp", I,
		   [sub ppExp exp, sub ppAtExp atexp])
      | ppExp(out, i, COLONExp(I, exp, ty)) =
	    ppElem(out, i, "COLONExp", I,
		   [sub ppExp exp, sub ppTy ty])
      | ppExp(out, i, HANDLEExp(I, exp, match)) =
	    ppElem(out, i, "HANDLEExp", I,
		   [sub ppExp exp, sub ppMatch match])
      | ppExp(out, i, RAISEExp(I, exp)) =
	    ppElem(out, i, "RAISEExp", I,
		   [sub ppExp exp])
      | ppExp(out, i, FNExp(I, match)) =
	    ppElem(out, i, "FNExp", I,
		   [sub ppMatch match])


    (* Matches *)

    and ppMatch(out, i, Match(I, mrule, match_opt)) =
	    ppElem(out, i, "Match", I,
		   [sub ppMrule mrule, subo ppMatch match_opt])

    and ppMrule(out, i, Mrule(I, pat, exp)) =
	    ppElem(out, i, "Mrule", I,
		   [sub ppPat pat, sub ppExp exp])


    (* Declarations *)

    and ppDec(out, i, VALDec(I, tyvarseq, valbind)) =
	    ppElem(out, i, "VALDec", I,
		   [sub ppTyVarseq tyvarseq, sub ppValBind valbind])
      | ppDec(out, i, TYPEDec(I, typbind)) =
	    ppElem(out, i, "TYPEDec", I,
		   [sub ppTypBind typbind])
      | ppDec(out, i, DATATYPEDec(I, datbind)) =
	    ppElem(out, i, "DATATYPEDec", I,
		   [sub ppDatBind datbind])
      | ppDec(out, i, DATATYPE2Dec(I, tycon, longtycon)) =
	    ppElem(out, i, "DATATYPE2Dec", I,
		   [sub ppTyCon tycon, sub ppLongTyCon longtycon])
      | ppDec(out, i, ABSTYPEDec(I, datbind, dec)) =
	    ppElem(out, i, "ABSTYPEDec", I,
		   [sub ppDatBind datbind, sub ppDec dec])
      | ppDec(out, i, EXCEPTIONDec(I, exbind)) =
	    ppElem(out, i, "EXCEPTIONDec", I,
		   [sub ppExBind exbind])
      | ppDec(out, i, LOCALDec(I, dec1, dec2)) =
	    ppElem(out, i, "LOCALDec", I,
		   [sub ppDec dec1, sub ppDec dec2])
      | ppDec(out, i, OPENDec(I, longstrids)) =
	    ppElem(out, i, "OPENDec", I,
		   [subs ppLongStrId longstrids])
      | ppDec(out, i, EMPTYDec(I)) =
	    ppElem(out, i, "EMPTYDec", I, [])
      | ppDec(out, i, SEQDec(I, dec1, dec2)) =
	    ppElem(out, i, "SEQDec", I,
		   [sub ppDec dec1, sub ppDec dec2])

    and ppValBind(out, i, PLAINValBind(I, pat, exp, valbind_opt)) =
	    ppElem(out, i, "PLAINValBind", I,
		   [sub ppPat pat, sub ppExp exp, subo ppValBind valbind_opt])
      | ppValBind(out, i, RECValBind(I, valbind)) =
	    ppElem(out, i, "RECValBind", I,
		   [sub ppValBind valbind])
    and ppTypBind(out, i, TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
	    ppElem(out, i, "TypBind", I,
		   [sub ppTyVarseq tyvarseq, sub ppTyCon tycon, sub ppTy ty,
		    subo ppTypBind typbind_opt])
    and ppDatBind(out, i, DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	    ppElem(out, i, "DatBind", I,
		   [sub ppTyVarseq tyvarseq, sub ppTyCon tycon,
		    sub ppConBind conbind, subo ppDatBind datbind_opt])
    and ppConBind(out, i, ConBind(I, _, vid, ty_opt, conbind_opt)) =
	    ppElem(out, i, "ConBind", I,
		   [sub ppVId vid, subo ppTy ty_opt,
		    subo ppConBind conbind_opt])
    and ppExBind(out, i, NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
	    ppElem(out, i, "NEWExBind", I,
		   [sub ppVId vid, subo ppTy ty_opt,
		    subo ppExBind exbind_opt])
      | ppExBind(out, i, EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
	    ppElem(out, i, "EQUALExBind", I,
		   [sub ppVId vid, sub ppLongVId longvid,
		    subo ppExBind exbind_opt])


    (* Patterns *)

    and ppAtPat(out, i, WILDCARDAtPat(I)) =
	    ppElem(out, i, "WILDCARDAtPat", I, [])
      | ppAtPat(out, i, SCONAtPat(I, scon)) =
	    ppElem(out, i, "SCONAtPat", I,
		   [sub ppSCon scon])
      | ppAtPat(out, i, IDAtPat(I, _, longvid)) =
	    ppElem(out, i, "IDAtPat", I,
		   [sub ppLongVId longvid])
      | ppAtPat(out, i, RECORDAtPat(I, patrow_opt)) =
	    ppElem(out, i, "RECORDAtPat", I,
		   [subo ppPatRow patrow_opt])
      | ppAtPat(out, i, PARAtPat(I, pat)) =
	    ppElem(out, i, "PARAtPat", I,
		   [sub ppPat pat])

    and ppPatRow(out, i, DOTSPatRow(I)) =
	    ppElem(out, i, "DOTSPatRow", I, [])
      | ppPatRow(out, i, FIELDPatRow(I, lab, pat, patrow_opt)) =
	    ppElem(out, i, "FIELDPatRow", I,
		   [sub ppLab lab, sub ppPat pat, subo ppPatRow patrow_opt])

    and ppPat(out, i, ATPat(I, atpat)) =
	    ppElem(out, i, "ATPat", I,
		   [sub ppAtPat atpat])
      | ppPat(out, i, CONPat(I, _, longvid, atpat)) =
	    ppElem(out, i, "CONPat", I,
		   [sub ppLongVId longvid, sub ppAtPat atpat])
      | ppPat(out, i, COLONPat(I, pat, ty)) =
	    ppElem(out, i, "COLONPat", I,
		   [sub ppPat pat, sub ppTy ty])
      | ppPat(out, i, ASPat(I, _, vid, ty_opt, pat)) =
	    ppElem(out, i, "ASPat", I,
		   [sub ppVId vid, subo ppTy ty_opt, sub ppPat pat])

    (* Level *)

    and ppLevel(out, i, lv) = ppAtom(out, i, "Lv", Level.toString lv)

    (* Type expressions *)

    and ppTy(out, i, VARTy(I, tyvar)) =
	    ppElem(out, i, "VARTy", I,
		   [sub ppTyVar tyvar])
      | ppTy(out, i, RECORDTy(I, tyrow_opt, level)) =
	    ppElem(out, i, "RECORDTy", I,
		   [subo ppTyRow tyrow_opt, sub ppLevel level])
      | ppTy(out, i, CONTy(I, tyseq, longtycon, level)) =
	    ppElem(out, i, "CONTy", I,
		   [sub ppTyseq tyseq, sub ppLongTyCon longtycon, sub ppLevel level])
      | ppTy(out, i, ARROWTy(I, ty1, ty2, mode, level)) =
	    ppElem(out, i, "ARROWTy", I,
		   [sub ppTy ty1, sub ppLevel mode, sub ppTy ty2, sub ppLevel level])
      | ppTy(out, i, PARTy(I, ty)) =
	    ppElem(out, i, "PARTy", I,
		   [sub ppTy ty])

    and ppTyRow(out, i, TyRow(I, lab, ty, tyrow_opt)) =
	    ppElem(out, i, "TyRow", I,
		   [sub ppLab lab, sub ppTy ty, subo ppTyRow tyrow_opt])


    (* Sequences *)

    and ppTyseq(out, i, Tyseq(I, tys)) =
	    ppElem(out, i, "Tyseq", I,
		   [subs ppTy tys])

    and ppTyVarseq(out, i, TyVarseq(I, tyvars)) =
	    ppElem(out, i, "TyVarseq", I,
		   [subs ppTyVar tyvars])
end;
