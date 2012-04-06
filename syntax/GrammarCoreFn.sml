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

functor GrammarCoreFn(type Info) : GRAMMAR_CORE =
struct
    (* Import *)

    type Info		= Info

    type SCon		= SCon.SCon
    type Lab		= Lab.Lab
    type VId		= VId.Id
    type TyCon		= TyCon.Id
    type TyVar		= TyVar.TyVar
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
	| RECORDTy       of Info * TyRow option
	| CONTy          of Info * Tyseq * longTyCon
	| ARROWTy        of Info * Ty * Ty
	| PARTy          of Info * Ty

    and TyRow =
	  TyRow          of Info * Lab * Ty * TyRow option

    (* Sequences [Section 2.8] *)

    and Tyseq =
	  Tyseq          of Info * Ty list

    and TyVarseq =
	  TyVarseq       of Info * TyVar list



    (* Extracting info fields *)

    fun infoAtExp(SCONAtExp(I,_))		= I
      | infoAtExp(IDAtExp(I,_,_))		= I
      | infoAtExp(RECORDAtExp(I,_))		= I
      | infoAtExp(LETAtExp(I,_,_))		= I
      | infoAtExp(PARAtExp(I,_))		= I

    fun infoExpRow(ExpRow(I,_,_,_))		= I

    fun infoExp(ATExp(I,_))			= I
      | infoExp(APPExp(I,_,_))			= I
      | infoExp(COLONExp(I,_,_))		= I
      | infoExp(HANDLEExp(I,_,_))		= I
      | infoExp(RAISEExp(I,_))			= I
      | infoExp(FNExp(I,_))			= I

    fun infoMatch(Match(I,_,_))			= I

    fun infoMrule(Mrule(I,_,_))			= I

    fun infoDec(VALDec(I,_,_))			= I
      | infoDec(TYPEDec(I,_))			= I
      | infoDec(DATATYPEDec(I,_))		= I
      | infoDec(DATATYPE2Dec(I,_,_))		= I
      | infoDec(ABSTYPEDec(I,_,_))		= I
      | infoDec(EXCEPTIONDec(I,_))		= I
      | infoDec(LOCALDec(I,_,_))		= I
      | infoDec(OPENDec(I,_))			= I
      | infoDec(EMPTYDec(I))			= I
      | infoDec(SEQDec(I,_,_))			= I

    fun infoValBind(PLAINValBind(I,_,_,_))	= I
      | infoValBind(RECValBind(I,_))		= I

    fun infoTypBind(TypBind(I,_,_,_,_))		= I

    fun infoDatBind(DatBind(I,_,_,_,_))		= I

    fun infoConBind(ConBind(I,_,_,_,_))		= I

    fun infoExBind(NEWExBind(I,_,_,_,_))	= I
      | infoExBind(EQUALExBind(I,_,_,_,_,_))	= I

    fun infoAtPat(WILDCARDAtPat(I))		= I
      | infoAtPat(SCONAtPat(I,_))		= I
      | infoAtPat(IDAtPat(I,_,_))		= I
      | infoAtPat(RECORDAtPat(I,_))		= I
      | infoAtPat(PARAtPat(I,_))		= I

    fun infoPatRow(DOTSPatRow(I))		= I
      | infoPatRow(FIELDPatRow(I,_,_,_))	= I

    fun infoPat(ATPat(I,_))			= I
      | infoPat(CONPat(I,_,_,_))		= I
      | infoPat(COLONPat(I,_,_))		= I
      | infoPat(ASPat(I,_,_,_,_))		= I

    fun infoTy(VARTy(I,_))			= I
      | infoTy(RECORDTy(I,_))			= I
      | infoTy(CONTy(I,_,_))			= I
      | infoTy(ARROWTy(I,_,_))			= I
      | infoTy(PARTy(I,_))			= I

    fun infoTyRow(TyRow(I,_,_,_))		= I

    fun infoTyseq(Tyseq(I,_))			= I
    fun infoTyVarseq(TyVarseq(I,_))		= I
end;
