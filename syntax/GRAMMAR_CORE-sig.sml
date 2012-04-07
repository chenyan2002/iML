(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML abstract core grammar
 *
 * Definition, Section 2.8
 *
 * Note:
 *   This is the syntax used in the inference rules for the core [Definition,
 *   Sections 4.10 and 6.7]. It omits almost anything having to do with infixed
 *   identifiers:
 *     - fixity directives
 *     - infixed application
 *     - infixed value construction
 *   However, op prefixes are kept, since they are required for rebuilding the
 *   syntax tree during fixity resolution.
 *   Optional semicolons are also omitted.
 *)

signature GRAMMAR_CORE =
sig
    (* Import *)

    type Info

    type SCon		= SCon.SCon
    type Lab		= Lab.Lab
    type VId		= VId.Id
    type TyCon		= TyCon.Id
    type TyVar		= TyVar.TyVar
    type LvVar          = LvVar.LvVar
    type StrId		= StrId.Id
    type longVId	= LongVId.longId
    type longTyCon	= LongTyCon.longId
    type longStrId	= LongStrId.longId


    (* Optional keyword `op' *)

    datatype Op = SANSOp | WITHOp


    (* Expressions [Figures 2 and 4] *)

    datatype AtExp =
	  SCONAtExp      of Info * SCon
	| IDAtExp        of Info * Op * longVId
	| RECORDAtExp    of Info * ExpRow option
	| LETAtExp       of Info * Dec * Exp
	| PARAtExp       of Info * Exp

    and ExpRow =
	  ExpRow         of Info * Lab * Exp * ExpRow option

    and Exp =
	  ATExp          of Info * AtExp
	| APPExp         of Info * Exp * AtExp
	| COLONExp       of Info * Exp * Ty
	| HANDLEExp      of Info * Exp * Match
	| RAISEExp       of Info * Exp
	| FNExp          of Info * Match

    (* Matches [Figures 2 and 4] *)

    and Match =
	  Match          of Info * Mrule * Match option

    and Mrule =
	  Mrule          of Info * Pat * Exp

    (* Declarations [Figures 2 and 4] *)

    and Dec =
	  VALDec         of Info * TyVarseq * ValBind
	| TYPEDec        of Info * TypBind
	| DATATYPEDec    of Info * DatBind
	| DATATYPE2Dec   of Info * TyCon * longTyCon
	| ABSTYPEDec     of Info * DatBind * Dec
	| EXCEPTIONDec   of Info * ExBind
	| LOCALDec       of Info * Dec * Dec
	| OPENDec        of Info * longStrId list
	| EMPTYDec       of Info
	| SEQDec         of Info * Dec * Dec

    (* Bindings [Figures 2 and 4] *)

    and ValBind =
	  PLAINValBind   of Info * Pat * Exp * ValBind option
	| RECValBind     of Info * ValBind

    and TypBind =
	  TypBind        of Info * TyVarseq * TyCon * Ty * TypBind option

    and DatBind =
	  DatBind        of Info * TyVarseq * TyCon * ConBind * DatBind option

    and ConBind =
	  ConBind        of Info * Op * VId * Ty option * ConBind option

    and ExBind =
	  NEWExBind      of Info * Op * VId * Ty option * ExBind option
	| EQUALExBind    of Info * Op * VId * Op * longVId * ExBind option

    (* Patterns [Figures 2 and 3] *)

    and AtPat =
	  WILDCARDAtPat  of Info
	| SCONAtPat      of Info * SCon
	| IDAtPat        of Info * Op * longVId
	| RECORDAtPat    of Info * PatRow option
	| PARAtPat       of Info * Pat

    and PatRow =
	  DOTSPatRow     of Info
	| FIELDPatRow    of Info * Lab * Pat * PatRow option

    and Pat =
	  ATPat          of Info * AtPat
	| CONPat         of Info * Op * longVId * AtPat
	| COLONPat       of Info * Pat * Ty
	| ASPat          of Info * Op * VId * Ty option * Pat

    (* Type expressions [Figures 2 and 3] *)

    and Ty =
	  VARTy          of Info * TyVar
	| RECORDTy       of Info * TyRow option * Level.t
	| CONTy          of Info * Tyseq * longTyCon * Level.t
	| ARROWTy        of Info * Ty * Ty * Level.t * Level.t  (* mode,outer *)
	| PARTy          of Info * Ty

    and TyRow =
	  TyRow          of Info * Lab * Ty * TyRow option

    (* Sequences [Section 2.8] *)

    and Tyseq =
	  Tyseq          of Info * Ty list

    and TyVarseq =
	  TyVarseq       of Info * TyVar list


    (* Operations *)

    val infoAtExp :	AtExp	-> Info
    val infoExpRow :	ExpRow	-> Info
    val infoExp :	Exp	-> Info
    val infoMatch :	Match	-> Info
    val infoMrule :	Mrule	-> Info
    val infoDec :	Dec	-> Info
    val infoValBind :	ValBind	-> Info
    val infoTypBind :	TypBind	-> Info
    val infoDatBind :	DatBind	-> Info
    val infoConBind :	ConBind	-> Info
    val infoExBind :	ExBind	-> Info
    val infoAtPat :	AtPat	-> Info
    val infoPatRow :	PatRow	-> Info
    val infoPat :	Pat	-> Info
    val infoTy :	Ty	-> Info
    val infoTyRow :	TyRow	-> Info
    val infoTyseq :	Tyseq	-> Info
    val infoTyVarseq :	TyVarseq -> Info
end;
