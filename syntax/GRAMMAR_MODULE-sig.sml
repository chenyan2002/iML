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

signature GRAMMAR_MODULE =
sig
    (* Import *)

    structure Core : GRAMMAR_CORE

    type Info

    type VId		= Core.VId
    type TyCon		= Core.TyCon
    type TyVar		= Core.TyVar
    type StrId		= Core.StrId
    type longVId	= Core.longVId
    type longTyCon	= Core.longTyCon
    type longStrId	= Core.longStrId
    type Dec		= Core.Dec
    type Ty		= Core.Ty
    type TyVarseq	= Core.TyVarseq

    type SigId		= SigId.Id
    type FunId		= FunId.Id


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


    (* Operations *)

    val infoStrExp :	StrExp  -> Info
    val infoStrDec :	StrDec  -> Info
    val infoStrBind :	StrBind -> Info
    val infoSigExp :	SigExp  -> Info
    val infoSigDec :	SigDec  -> Info
    val infoSigBind :	SigBind -> Info
    val infoSpec :	Spec    -> Info
    val infoValDesc :	ValDesc -> Info
    val infoTypDesc :	TypDesc -> Info
    val infoDatDesc :	DatDesc -> Info
    val infoConDesc :	ConDesc -> Info
    val infoExDesc :	ExDesc  -> Info
    val infoStrDesc :	StrDesc -> Info
    val infoFunDec :	FunDec  -> Info
    val infoFunBind :	FunBind -> Info
    val infoTopDec :	TopDec  -> Info
end;
