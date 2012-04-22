(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core elaboration
 *
 * Definition, Sections 4.10, 4.11, 4.6, 4.7, 2.9
 *
 * Notes:
 *   - Elaboration also checks the further restrictions [Section 4.11].
 *   - To implement overloading resolution and checks for flexible records,
 *     we accumulate lists of unresolved types at each value declaration.
 *     This requires an additional argument to most elab functions.
 *   - To implement the 3rd restriction in 4.11 some elab functions are
 *     passed an additional boolean argument to recognise being on the toplevel.
 *   - The definition says that overloaded types get defaulted if the
 *     "surrounding text" does not resolve it. It leaves some freedom to
 *     how large this context may be. We choose the innermost value binding.
 *   - The definition states that "the program context" must determine the
 *     exact type of flexible records, but it does not say how large this
 *     context may be either. Again we choose the innermost surrounding value
 *     declaration.
 *)

structure FlowCore : FLOW_CORE =
struct
    (* Import *)

    open GrammarProgram
    open GrammarModule
    open GrammarCore

    open StaticObjectsCore
    open Error

    val getType = ElabCore.getType
    val setType = ElabCore.setType
    val getScheme = ElabCore.getScheme

    fun getLv tau =
      case !tau of
        RowType (_,_,lv) => lv
      | FunType (_,_,_,lv) => lv
      | ConsType (_,_,lv) => lv
      | Determined tau => getLv tau
      | _ => ref Level.Unknown

    fun getASTLv ty = case ty of
        RECORDTy (_,_,lv) => lv
      | CONTy (_,_,_,lv) => lv
      | ARROWTy (_,_,_,_,lv) => lv
      | PARTy (_,ty) => getASTLv ty
      | VARTy _ => Level.Unknown

    fun loopOpt f opt = case opt of
                          NONE => ()
                        | SOME opt => f opt


    (* Core *)

   (* Expressions *)

    fun loopAtExp atexp =
      case atexp of
        SCONAtExp(I, scon) => ()
      | IDAtExp(I, _, longvid) => ()
      | RECORDAtExp(I, exprow_opt) => loopOpt loopExpRow exprow_opt 
      | LETAtExp(I, dec, exp) => (
          loopDec dec; 
          loopExp exp)
      | PARAtExp(I, exp) => loopExp exp

    and loopExpRow (ExpRow(I, lab, exp, exprow_opt)) =
          loopOpt loopExpRow exprow_opt

    and loopExp (ATExp(I, atexp)) = loopAtExp atexp
      | loopExp (APPExp(I, exp, atexp)) = (loopExp exp; loopAtExp atexp)
      | loopExp (COLONExp(I, exp, ty)) = loopExp exp
      | loopExp (HANDLEExp(I, exp, match)) = (loopExp exp; loopMatch match)
      | loopExp (RAISEExp(I, exp)) = loopExp exp
      | loopExp (FNExp(I, match)) = loopMatch match

    (* Matches *)

    and loopMatch (Match(I, mrule, match_opt)) = 
        (loopMrule mrule; 
         loopOpt loopMatch match_opt)
    and loopMrule (Mrule(I, pat, exp)) = 
        (loopPat pat;
         loopExp exp)

    (* Declarations *)

    and loopDec (VALDec(I, tyvarseq, valbind)) = loopValBind valbind
      | loopDec (TYPEDec(I, typbind)) = loopTypBind typbind
      | loopDec (DATATYPEDec(I, datbind)) = loopDatBind datbind
      | loopDec (DATATYPE2Dec(I, tycon, longtycon)) = ()
      | loopDec (ABSTYPEDec(I, datbind, dec)) = (loopDatBind datbind; loopDec dec)
      | loopDec (EXCEPTIONDec(I, exbind)) = loopExBind exbind
      | loopDec (LOCALDec(I, dec1, dec2)) = (loopDec dec1; loopDec dec2)
      | loopDec (OPENDec(I, longstrids)) = ()
      | loopDec (EMPTYDec(I)) = ()
      | loopDec (SEQDec(I, dec1, dec2)) = (loopDec dec1; loopDec dec2)

    and loopValBind (PLAINValBind(I, pat, exp, valbind_opt)) =
          (loopPat pat; loopExp exp; loopOpt loopValBind valbind_opt)
      | loopValBind (RECValBind(I, valbind)) = loopValBind valbind

    and loopTypBind (TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
          loopOpt loopTypBind typbind_opt
          
    and loopDatBind (DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
          loopOpt loopDatBind datbind_opt

    and loopConBind (ConBind(I, _, vid, ty_opt, conbind_opt)) =
          loopOpt loopConBind conbind_opt

    and loopExBind (NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
          loopOpt loopExBind exbind_opt
      | loopExBind (EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
          loopOpt loopExBind exbind_opt

    (* Patterns *)

    and loopAtPat (WILDCARDAtPat(I)) = ()
      | loopAtPat (SCONAtPat(I, scon)) = ()
      | loopAtPat (IDAtPat(I, _, longvid)) = ()
      | loopAtPat (RECORDAtPat(I, patrow_opt)) = 
          loopOpt loopPatRow patrow_opt
      | loopAtPat (PARAtPat(I, pat)) = loopPat pat

    and loopPatRow (DOTSPatRow(I)) = ()
      | loopPatRow (FIELDPatRow(I, lab, pat, patrow_opt)) =
          (loopPat pat;
           loopOpt loopPatRow patrow_opt)

    and loopPat (ATPat(I, atpat)) = loopAtPat atpat
      | loopPat (CONPat(I, _, longvid, atpat)) = loopAtPat atpat
      | loopPat (COLONPat(I, pat, ty)) = 
          (loopPat pat;
           getLv(getType I) := getASTLv ty)
      | loopPat (ASPat(I, _, vid, ty_opt, pat)) = loopPat pat

    (* Module *)

    (* Structures *)

    fun loopStrDec (DECStrDec(I, dec)) = loopDec dec
      | loopStrDec (STRUCTUREStrDec(I, strbind)) = loopStrBind strbind
      | loopStrDec (LOCALStrDec(I, strdec1, strdec2)) = 
          (loopStrDec strdec1; loopStrDec strdec2)
      | loopStrDec (EMPTYStrDec(I)) = ()
      | loopStrDec (SEQStrDec(I, strdec1, strdec2)) = 
          (loopStrDec strdec1; loopStrDec strdec2)

    and loopStrBind (StrBind(I, strid, strexp, strbind_opt)) =
          (loopStrExp strexp; 
           loopOpt loopStrBind strbind_opt)

    and loopStrExp (STRUCTStrExp(I, strdec)) = loopStrDec strdec
      | loopStrExp (IDStrExp(I, longstrid)) = ()
      | loopStrExp (COLONStrExp(I, strexp, sigexp)) = loopStrExp strexp
      | loopStrExp (SEALStrExp(I, strexp, sigexp)) = loopStrExp strexp
      | loopStrExp (APPStrExp(I, funid, strexp)) = loopStrExp strexp
      | loopStrExp (LETStrExp(I, strdec, strexp)) = (loopStrDec strdec; loopStrExp strexp)

    (* Top-level declarations *)

    and loopTopDec (STRDECTopDec(I, strdec, topdec_opt)) = 
          (loopStrDec strdec;
           loopOpt loopTopDec topdec_opt)
      | loopTopDec (SIGDECTopDec(I, sigdec, topdec_opt)) = loopOpt loopTopDec topdec_opt
      | loopTopDec _ = ()

    (* Programs *)

    fun loopProgram (Program(I, topdec, program_opt)) =
        (loopTopDec topdec;
         loopOpt loopProgram program_opt)

end;
