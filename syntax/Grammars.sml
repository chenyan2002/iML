(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML grammar
 *)

structure GrammarCore    = GrammarCoreFn(type Info = Source.info)

structure GrammarModule  = GrammarModuleFn(type Info = Source.info
					   structure Core = GrammarCore)

structure GrammarProgram = GrammarProgramFn(type Info = Source.info
					    structure Module = GrammarModule);

 fun foreach {prog: GrammarModule.TopDec,
              handleI: Source.info -> unit,
              handlePat: GrammarCore.Pat -> unit
             } =
   let
     open GrammarProgram
     open GrammarModule
     open GrammarCore

    fun loopOpt f opt = case opt of
                          NONE => ()
                        | SOME opt => f opt

    (* Core *)

   (* Expressions *)

    fun loopAtExp atexp =
      (handleI(infoAtExp atexp);
      case atexp of
        SCONAtExp(I, scon) => ()
      | IDAtExp(I, _, longvid) => ()
      | RECORDAtExp(I, exprow_opt) => loopOpt loopExpRow exprow_opt 
      | LETAtExp(I, dec, exp) => (
          loopDec dec; 
          loopExp exp)
      | PARAtExp(I, exp) => loopExp exp)

    and loopExpRow (ExpRow(I, lab, exp, exprow_opt)) =
          (handleI(I);
           loopOpt loopExpRow exprow_opt)

    and loopExp exp =
        (handleI(infoExp exp);
         case exp of
           (ATExp(I, atexp)) => loopAtExp atexp
         | (APPExp(I, exp, atexp)) => (loopExp exp; loopAtExp atexp)
         | (COLONExp(I, exp, ty)) => loopExp exp
         | (HANDLEExp(I, exp, match)) => (loopExp exp; loopMatch match)
         | (RAISEExp(I, exp)) => loopExp exp
         | (FNExp(I, match)) => loopMatch match)

    (* Matches *)

    and loopMatch (Match(I, mrule, match_opt)) = 
        (handleI(I);
         loopMrule mrule; 
         loopOpt loopMatch match_opt)
    and loopMrule (Mrule(I, pat, exp)) = 
        (handleI(I);
         loopPat pat;
         loopExp exp)

    (* Declarations *)

    and loopDec dec =
        (handleI(infoDec dec);
         case dec of
           (VALDec(I, tyvarseq, valbind)) => loopValBind valbind
         | (TYPEDec(I, typbind)) => loopTypBind typbind
         | (DATATYPEDec(I, datbind)) => loopDatBind datbind
         | (DATATYPE2Dec(I, tycon, longtycon)) => ()
         | (ABSTYPEDec(I, datbind, dec)) => (loopDatBind datbind; loopDec dec)
         | (EXCEPTIONDec(I, exbind)) => loopExBind exbind
         | (LOCALDec(I, dec1, dec2)) => (loopDec dec1; loopDec dec2)
         | (OPENDec(I, longstrids)) => ()
         | (EMPTYDec(I)) => ()
         | (SEQDec(I, dec1, dec2)) => (loopDec dec1; loopDec dec2))

    and loopValBind (PLAINValBind(I, pat, exp, valbind_opt)) =
          (handleI(I); loopPat pat; loopExp exp; loopOpt loopValBind valbind_opt)
      | loopValBind (RECValBind(I, valbind)) = (handleI(I); loopValBind valbind)

    and loopTypBind (TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
          (handleI(I); loopOpt loopTypBind typbind_opt)
          
    and loopDatBind (DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
          (handleI(I); loopOpt loopDatBind datbind_opt)

    and loopConBind (ConBind(I, _, vid, ty_opt, conbind_opt)) =
          (handleI(I); loopOpt loopConBind conbind_opt)

    and loopExBind (NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
          (handleI(I); loopOpt loopExBind exbind_opt)
      | loopExBind (EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
          (handleI(I); loopOpt loopExBind exbind_opt)

    (* Patterns *)

    and loopAtPat atpat =
        (handleI(infoAtPat atpat);
         case atpat of
           (WILDCARDAtPat(I)) => ()
         | (SCONAtPat(I, scon)) => ()
         | (IDAtPat(I, _, longvid)) => ()
         | (RECORDAtPat(I, patrow_opt)) => 
             loopOpt loopPatRow patrow_opt
         | (PARAtPat(I, pat)) => loopPat pat)
                                
    and loopPatRow (DOTSPatRow(I)) = handleI(I)
      | loopPatRow (FIELDPatRow(I, lab, pat, patrow_opt)) =
          (handleI(I);
           loopPat pat;
           loopOpt loopPatRow patrow_opt)

    and loopPat pat =
        (handleI(infoPat pat);
         handlePat(pat);
         case pat of 
           (ATPat(I, atpat)) => loopAtPat atpat
         | (CONPat(I, _, longvid, atpat)) => loopAtPat atpat
         | (COLONPat(I, pat, ty)) => loopPat pat
         | (ASPat(I, _, vid, ty_opt, pat)) => loopPat pat)

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
   in
     loopTopDec(prog)
   end
