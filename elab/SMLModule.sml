(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract module grammar
 *)

structure SMLModule : SML_MODULE =
struct
    (* Import *)

    open GrammarModule
    open PPGrammar

    structure PPCore = SMLCore

    (* Identifiers *)

    fun ppSigId(out, i, sigid) = ppAtom(out, i, "SigId", SigId.toString sigid)
    fun ppFunId(out, i, funid) = ppAtom(out, i, "FunId", FunId.toString funid)


    (* Structures *)

    fun ppStrExp(out, i, STRUCTStrExp(I, strdec)) =
	    ppElem(out, i, "STRUCTStrExp", I,
		   [sub ppStrDec strdec])
      | ppStrExp(out, i, IDStrExp(I, longstrid)) =
	    ppElem(out, i, "IDStrExp", I,
		   [sub PPCore.ppLongStrId longstrid])
      | ppStrExp(out, i, COLONStrExp(I, strexp, sigexp)) =
	    ppElem(out, i, "COLONStrExp", I,
		   [sub ppStrExp strexp, sub ppSigExp sigexp])
      | ppStrExp(out, i, SEALStrExp(I, strexp, sigexp)) =
	    ppElem(out, i, "SEALStrExp", I,
		   [sub ppStrExp strexp, sub ppSigExp sigexp])
      | ppStrExp(out, i, APPStrExp(I, funid, strexp)) =
	    ppElem(out, i, "APPStrExp", I,
		   [sub ppFunId funid, sub ppStrExp strexp])
      | ppStrExp(out, i, LETStrExp(I, strdec, strexp)) =
	    ppElem(out, i, "LETStrExp", I,
		   [sub ppStrDec strdec, sub ppStrExp strexp])

    and ppStrDec(out, i, DECStrDec(I, dec)) =
	    ppElem(out, i, "DECStrDec", I,
		   [sub PPCore.ppDec dec])
      | ppStrDec(out, i, STRUCTUREStrDec(I, strbind)) =
	    ppElem(out, i, "STRUCTUREStrDec", I,
		   [sub ppStrBind strbind])
      | ppStrDec(out, i, LOCALStrDec(I, strdec1, strdec2)) =
	    ppElem(out, i, "LOCALStrDec", I,
		   [sub ppStrDec strdec1, sub ppStrDec strdec2])
      | ppStrDec(out, i, EMPTYStrDec(I)) =
	    ppElem(out, i, "EMPTYStrDec", I, [])
      | ppStrDec(out, i, SEQStrDec(I, strdec1, strdec2)) =
	    ppElem(out, i, "SEQStrDec", I,
		   [sub ppStrDec strdec1, sub ppStrDec strdec2])

    and ppStrBind(out, i, StrBind(I, strid, strexp, strbind_opt)) =
	    ppElem(out, i, "StrBind", I,
		   [sub PPCore.ppStrId strid, sub ppStrExp strexp,
		    subo ppStrBind strbind_opt])


    (* Signatures *)

    and ppSigExp(out, i, SIGSigExp(I, spec)) =
	    ppElem(out, i, "SIGSigExp", I,
		   [sub ppSpec spec])
      | ppSigExp(out, i, IDSigExp(I, sigid)) =
	    ppElem(out, i, "IDSigExp", I,
		   [sub ppSigId sigid])
      | ppSigExp(out, i, WHERETYPESigExp(I, sigexp, tyvarseq, longtycon, ty)) =
	    ppElem(out, i, "WHERETYPESigExp", I,
		   [sub ppSigExp sigexp, sub PPCore.ppTyVarseq tyvarseq,
		    sub PPCore.ppLongTyCon longtycon, sub PPCore.ppTy ty])

    and ppSigDec(out, i, SigDec(I, sigbind)) =
	    ppElem(out, i, "SigDec", I,
		   [sub ppSigBind sigbind])

    and ppSigBind(out, i, SigBind(I, sigid, sigexp, sigbind_opt)) =
	    ppElem(out, i, "SigBind", I,
		   [sub ppSigId sigid, sub ppSigExp sigexp,
		    subo ppSigBind sigbind_opt])


    (* Specifications *)

    and ppSpec(out, i, VALSpec(I, valdesc)) =
	    ppElem(out, i, "VALSpec", I,
		   [sub ppValDesc valdesc])
      | ppSpec(out, i, TYPESpec(I, typdesc)) =
	    ppElem(out, i, "TYPESpec", I,
		   [sub ppTypDesc typdesc])
      | ppSpec(out, i, EQTYPESpec(I, typdesc)) =
	    ppElem(out, i, "EQTYPESpec", I,
		   [sub ppTypDesc typdesc])
      | ppSpec(out, i, DATATYPESpec(I, datdesc)) =
	    ppElem(out, i, "DATATYPESpec", I,
		   [sub ppDatDesc datdesc])
      | ppSpec(out, i, DATATYPE2Spec(I, tycon, longtycon)) =
	    ppElem(out, i, "DATATYPE2Spec", I,
		   [sub PPCore.ppTyCon tycon, sub PPCore.ppLongTyCon longtycon])
      | ppSpec(out, i, EXCEPTIONSpec(I, exdesc)) =
	    ppElem(out, i, "EXCEPTIONSpec", I,
		   [sub ppExDesc exdesc])
      | ppSpec(out, i, STRUCTURESpec(I, strdesc)) =
	    ppElem(out, i, "STRUCTURESpec", I,
		   [sub ppStrDesc strdesc])
      | ppSpec(out, i, INCLUDESpec(I, sigexp)) =
	    ppElem(out, i, "INCLUDESpec", I,
		   [sub ppSigExp sigexp])
      | ppSpec(out, i, EMPTYSpec(I)) =
	    ppElem(out, i, "EMPTYSpec", I, [])
      | ppSpec(out, i, SEQSpec(I, spec1, spec2)) =
	    ppElem(out, i, "SEQSpec", I,
		   [sub ppSpec spec1, sub ppSpec spec2])
      | ppSpec(out, i, SHARINGTYPESpec(I, spec, longtycons)) =
	    ppElem(out, i, "SHARINGTYPESpec", I,
		   [sub ppSpec spec, subs PPCore.ppLongTyCon longtycons])
      | ppSpec(out, i, SHARINGSpec(I, spec, longstrids)) =
	    ppElem(out, i, "SHARINGSpec", I,
		   [sub ppSpec spec, subs PPCore.ppLongStrId longstrids])

    and ppValDesc(out, i, ValDesc(I, vid, ty, valdesc_opt)) =
	    ppElem(out, i, "ValDesc", I,
		   [sub PPCore.ppVId vid, sub PPCore.ppTy ty,
		    subo ppValDesc valdesc_opt])
    and ppTypDesc(out, i, TypDesc(I, tyvarseq, tycon, typdesc_opt)) =
	    ppElem(out, i, "TypDec", I,
		   [sub PPCore.ppTyVarseq tyvarseq, sub PPCore.ppTyCon tycon,
		    subo ppTypDesc typdesc_opt])
    and ppDatDesc(out, i, DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	    ppElem(out, i, "DatDesc", I,
		   [sub PPCore.ppTyVarseq tyvarseq, sub PPCore.ppTyCon tycon,
		    sub ppConDesc condesc, subo ppDatDesc datdesc_opt])
    and ppConDesc(out, i, ConDesc(I, vid, ty_opt, condesc_opt)) =
	    ppElem(out, i, "ConDesc", I,
		   [sub PPCore.ppVId vid, subo PPCore.ppTy ty_opt,
		    subo ppConDesc condesc_opt])
    and ppExDesc(out, i, ExDesc(I, vid, ty_opt, exdesc_opt)) =
	    ppElem(out, i, "ExDesc", I,
		   [sub PPCore.ppVId vid, subo PPCore.ppTy ty_opt,
		    subo ppExDesc exdesc_opt])
    and ppStrDesc(out, i, StrDesc(I, strid, sigexp, strdesc_opt)) =
	    ppElem(out, i, "StrDesc", I,
		   [sub PPCore.ppStrId strid, sub ppSigExp sigexp,
		    subo ppStrDesc strdesc_opt])


    (* Functors *)

    and ppFunDec(out, i, FunDec(I, funbind)) =
	    ppElem(out, i, "FunDec", I,
		   [sub ppFunBind funbind])

    and ppFunBind(out, i, FunBind(I, funid, strid, sigexp, strexp,
				  funbind_opt)) =
	    ppElem(out, i, "FunBind", I,
		   [sub ppFunId funid, sub PPCore.ppStrId strid,
		    sub ppSigExp sigexp, sub ppStrExp strexp,
		    subo ppFunBind funbind_opt])


    (* Top-level declarations *)

    and ppTopDec(out, i, STRDECTopDec(I, strdec, topdec_opt)) =
	    ppElem(out, i, "STRDECTopDec", I,
		   [sub ppStrDec strdec, subo ppTopDec topdec_opt])
      | ppTopDec(out, i, SIGDECTopDec(I, sigdec, topdec_opt)) =
	    ppElem(out, i, "SIGDECTopDec", I,
		   [sub ppSigDec sigdec, subo ppTopDec topdec_opt])
      | ppTopDec(out, i, FUNDECTopDec(I, fundec, topdec_opt)) =
	    ppElem(out, i, "FUNDECTopDec", I,
		   [sub ppFunDec fundec, subo ppTopDec topdec_opt])
end;
