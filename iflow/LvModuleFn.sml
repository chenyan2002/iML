(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML abstract module grammar
 *
 * Definition, Section 3.4
 *
 * Notes:
 *   This is the syntax used in the inference rules for modules [Definition,
 *   Sections 5.7 and 7.3]. Optional semicolons are omitted.
 *   The structure sharing derived form [Definition, Appendix A] has been added,
 *   because it cannot be derived purely syntactically.
 *)

functor LvModuleFn(type Info
			structure Core : GRAMMAR_CORE
		       ) : LV_MODULE =
struct
    (* Import *)

    structure Core = Core
    type      Info = Info

    open Core

    type SigId = SigId.Id
    type FunId = FunId.Id


    (* Structures [Figures 5 and 6] *)

    datatype StrExp =
	  STRUCTStrExp    of Info * StrDec
	| IDStrExp        of Info * longStrId
	| COLONStrExp     of Info * StrExp * SigExp
	| SEALStrExp      of Info * StrExp * SigExp
	| APPStrExp       of Info * FunId * StrExp
	| LETStrExp       of Info * StrDec * StrExp

    and StrDec =
          DECStrDec       of Info * Dec
        | STRUCTUREStrDec of Info * StrBind
        | LOCALStrDec     of Info * StrDec * StrDec
        | EMPTYStrDec     of Info
        | SEQStrDec       of Info * StrDec * StrDec

    and StrBind =
          StrBind         of Info * StrId * StrExp * StrBind option

    (* Signatures [Figures 5 and 6] *)

    and SigExp =
          SIGSigExp       of Info * Spec
        | IDSigExp        of Info * SigId
        | WHERETYPESigExp of Info * SigExp * TyVarseq * longTyCon * Ty

    and SigDec =
          SigDec          of Info * SigBind

    and SigBind =
          SigBind         of Info * SigId * SigExp * SigBind option

    (* Specifications [Figures 5 and 7] *)

    and Spec =
	  VALSpec         of Info * ValDesc
	| TYPESpec        of Info * TypDesc
	| EQTYPESpec      of Info * TypDesc
	| DATATYPESpec    of Info * DatDesc
	| DATATYPE2Spec   of Info * TyCon * longTyCon
	| EXCEPTIONSpec   of Info * ExDesc
	| STRUCTURESpec   of Info * StrDesc
	| INCLUDESpec     of Info * SigExp
	| EMPTYSpec       of Info
	| SEQSpec         of Info * Spec * Spec
	| SHARINGTYPESpec of Info * Spec * longTyCon list
	| SHARINGSpec     of Info * Spec * longStrId list

    and ValDesc =
	  ValDesc         of Info * VId * Ty * ValDesc option

    and TypDesc =
	  TypDesc         of Info * TyVarseq * TyCon * TypDesc option

    and DatDesc =
	  DatDesc         of Info * TyVarseq * TyCon * ConDesc * DatDesc option

    and ConDesc =
	  ConDesc         of Info * VId * Ty option * ConDesc option

    and ExDesc =
	  ExDesc          of Info * VId * Ty option * ExDesc option

    and StrDesc =
          StrDesc         of Info * StrId * SigExp * StrDesc option

    (* Functors [Figures 5 and 8] *)

    and FunDec =
          FunDec          of Info * FunBind

    and FunBind =
          FunBind         of Info * FunId * StrId * SigExp * StrExp
                                  * FunBind option

    (* Top-level declarations [Figures 5 and 8] *)

    and TopDec =
          STRDECTopDec    of Info * StrDec * TopDec option
        | SIGDECTopDec    of Info * SigDec * TopDec option
        | FUNDECTopDec    of Info * FunDec * TopDec option


    (* Extracting info fields *)

    fun infoStrExp(STRUCTStrExp(I,_))		= I
      | infoStrExp(IDStrExp(I,_))		= I
      | infoStrExp(COLONStrExp(I,_,_))		= I
      | infoStrExp(SEALStrExp(I,_,_))		= I
      | infoStrExp(APPStrExp(I,_,_))		= I
      | infoStrExp(LETStrExp(I,_,_))		= I

    fun infoStrDec(DECStrDec(I,_))		= I
      | infoStrDec(STRUCTUREStrDec(I,_))	= I
      | infoStrDec(LOCALStrDec(I,_,_))		= I
      | infoStrDec(EMPTYStrDec(I))		= I
      | infoStrDec(SEQStrDec(I,_,_))		= I

    fun infoStrBind(StrBind(I,_,_,_))		= I

    fun infoSigExp(SIGSigExp(I,_))		= I
      | infoSigExp(IDSigExp(I,_))		= I
      | infoSigExp(WHERETYPESigExp(I,_,_,_,_))	= I

    fun infoSigDec(SigDec(I,_))			= I

    fun infoSigBind(SigBind(I,_,_,_))		= I

    fun infoSpec(VALSpec(I,_))			= I
      | infoSpec(TYPESpec(I,_))			= I
      | infoSpec(EQTYPESpec(I,_))		= I
      | infoSpec(DATATYPESpec(I,_))		= I
      | infoSpec(DATATYPE2Spec(I,_,_))		= I
      | infoSpec(EXCEPTIONSpec(I,_))		= I
      | infoSpec(STRUCTURESpec(I,_))		= I
      | infoSpec(INCLUDESpec(I,_))		= I
      | infoSpec(EMPTYSpec(I))			= I
      | infoSpec(SEQSpec(I,_,_))		= I
      | infoSpec(SHARINGTYPESpec(I,_,_))	= I
      | infoSpec(SHARINGSpec(I,_,_))		= I

    fun infoValDesc(ValDesc(I,_,_,_))		= I
    fun infoTypDesc(TypDesc(I,_,_,_))		= I
    fun infoDatDesc(DatDesc(I,_,_,_,_))		= I
    fun infoConDesc(ConDesc(I,_,_,_))		= I
    fun infoExDesc(ExDesc(I,_,_,_))		= I
    fun infoStrDesc(StrDesc(I,_,_,_))		= I

    fun infoFunDec(FunDec(I,_))			= I

    fun infoFunBind(FunBind(I,_,_,_,_,_))	= I

    fun infoTopDec(STRDECTopDec(I,_,_))		= I
      | infoTopDec(SIGDECTopDec(I,_,_))		= I
      | infoTopDec(FUNDECTopDec(I,_,_))		= I
end;
