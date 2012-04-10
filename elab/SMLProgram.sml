
structure SMLProgram : SML_PROGRAM =
struct
    (* Import *)

    open GrammarProgram
    open GrammarModule
    open GrammarCore
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^

    (* Type Environment *)

    val B = ref InitialStaticBasis.B0
    val Env = fn () =>
      let
        val (TyName, FunEnv, SigEnv, Env) = !B
      in
        Env
      end
    fun tyVid vid = 
      case StaticEnv.findVId (Env(), vid) of
        NONE => empty
      | SOME (sigma, _) => text "***" ^/^ PPType.ppTypeScheme sigma
(*      | SOME (sigma, IdStatus.v) => PPType.ppTypeScheme sigma*)
    val red = str(chr(27))^"[31m"
    val black = str(chr(27))^"[0m"
    fun tyLongVid vid =
      case StaticEnv.findLongVId (Env(), vid) of
        NONE => empty
      | SOME (sigma,_) => hbox(text red ^/^ PPType.ppTypeScheme sigma ^/^ text black)

    (* Special constants *)

    fun ppSCon scon = text(SCon.toString scon)

    (* Identifiers *)

    val ppSigID = text o SigId.toString
    val ppFunId = text o FunId.toString
    fun ppLab lab     = text(Lab.toString lab)
    fun ppVId vid     = text(VId.toString vid) ^/^ tyVid vid
    fun ppTyVar tyvar = text(TyVar.toString tyvar)
    fun ppTyCon tycon = text(TyCon.toString tycon)
    fun ppStrId strid = text(StrId.toString strid)
    fun ppLvVar lvvar = text(LvVar.toString lvvar)
    fun ppLv lv       = text(Level.toString lv)

    fun ppLongVId longvid = text(LongVId.toString longvid) ^/^ tyLongVid longvid
    fun ppLongTyCon longtycon = text(LongTyCon.toString longtycon)
    fun ppLongStrId longstrid = text(LongStrId.toString longstrid)

    (* isTuple for label *)

    fun isTupleLab lab = 
      case Lab.compare (lab, Lab.fromString "A") of
        LESS => true
      | _ => false
    fun isTuple (SOME (ExpRow(_,lab,_,_))) = isTupleLab lab
      | isTuple NONE = true
    fun isPatTuple (SOME (FIELDPatRow(_, lab, _, patrow_opt))) = isTupleLab lab
      | isPatTuple (SOME _) = false
      | isPatTuple NONE = true
    fun isTyTuple (SOME (TyRow(_,lab,_,_))) = isTupleLab lab
      | isTyTuple NONE = true

    (* Core *)

   (* Expressions *)

    fun ppAtExp (SCONAtExp(I, scon)) = ppSCon scon
      | ppAtExp (IDAtExp(I, _, longvid)) = ppLongVId longvid
      | ppAtExp (RECORDAtExp(I, exprow_opt)) = 
          if isTuple(exprow_opt) then
            paren(ppOpt ppExpRow exprow_opt)
          else brace(ppOpt ppExpRow exprow_opt)
      | ppAtExp (LETAtExp(I, dec, exp)) =
          vbox(nest(break ^^ text "let" ^^ 
                 nest(break ^^ below(ppDec dec)) ^/^
               text "in" ^^
                 nest(break ^^ below(nest(ppExp exp))) ^/^
               text "end"))
      | ppAtExp (PARAtExp(I, exp)) = paren(ppExp exp)

    and ppExpRow (ExpRow(I, lab, exp, exprow_opt)) =
          (if (isTupleLab lab) then empty
          else ppLab lab ^/^ text "=") ^/^
          ppExp exp ^/^ 
          ppOpt (fn x => text "," ^/^ ppExpRow x) exprow_opt

    and ppExp (ATExp(I, atexp)) = hbox(ppAtExp atexp)
      | ppExp (APPExp(I, exp, atexp)) = hbox(ppExp exp ^/^ ppAtExp atexp)
      | ppExp (COLONExp(I, exp, ty)) = hbox(ppExp exp ^/^ text ":" ^/^ ppTy ty)
      | ppExp (HANDLEExp(I, exp, match)) = 
          hbox(ppExp exp ^/^ text "handle" ^/^ ppMatch match)
      | ppExp (RAISEExp(I, exp)) = hbox(text "raise" ^/^ ppExp exp)
      | ppExp (FNExp(I, match)) = hbox(text "fn" ^/^ ppMatch match)

    (* Matches *)

    and ppMatch (Match(I, mrule, match_opt)) = 
          vbox(ppMrule mrule ^/^ 
          ppOpt (fn x => hbox(text "|" ^/^ nest(ppMatch x))) match_opt)
    and ppMrule (Mrule(I, pat, exp)) = 
          abox(hbox(ppPat pat ^/^ text "=>") ^/^
               nest(hbox(ppExp exp)))

    (* Declarations *)

    and ppDec (VALDec(I, tyvarseq, valbind)) = 
          hbox(text "val" ^/^ ppTyVarseq tyvarseq ^/^ ppValBind valbind)
      | ppDec (TYPEDec(I, typbind)) =
          hbox(text "type" ^/^ ppTypBind typbind)
      | ppDec (DATATYPEDec(I, datbind)) =
          hbox(text "datatype" ^/^ ppDatBind datbind)
      | ppDec (DATATYPE2Dec(I, tycon, longtycon)) =
          hbox(text "datatype" ^/^ ppTyCon tycon ^/^ text "=" ^/^ ppLongTyCon longtycon)
      | ppDec (ABSTYPEDec(I, datbind, dec)) =
          hbox(text "abstype" ^/^ ppDatBind datbind ^/^ text "with" ^/^
          ppDec dec ^/^ text "end")
      | ppDec (EXCEPTIONDec(I, exbind)) =
          hbox(text "exception" ^/^ ppExBind exbind)
      | ppDec (LOCALDec(I, dec1, dec2)) =
          fbox(text "local" ^/^ 
               nest(ppDec dec1) ^/^ text "in" ^/^
               nest(ppDec dec2) ^/^ text "end")
      | ppDec (OPENDec(I, longstrids)) = 
          hbox(text "open" ^/^ ppCommaList ppLongStrId longstrids)
      | ppDec (EMPTYDec(I)) = empty
      | ppDec (SEQDec(I, dec1, dec2)) =
          vbox(hbox(ppDec dec1 ^^ text ";") ^/^ ppDec dec2)

    and ppValBind (PLAINValBind(I, pat, exp, valbind_opt)) =
          vbox(hbox(ppPat pat ^/^ text "=" ^/^ ppExp exp) ^/^ 
               ppOpt (fn x => hbox(text "and" ^/^ ppValBind x)) valbind_opt)
      | ppValBind (RECValBind(I, valbind)) = text "rec" ^/^ ppValBind valbind

    and ppTypBind (TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
          vbox(hbox(ppTyVarseq tyvarseq ^/^ ppTyCon tycon ^/^ text "=" ^/^ ppTy ty) ^/^ 
               ppOpt (fn x => hbox(text "and" ^/^ ppTypBind x)) typbind_opt)
          
    and ppDatBind (DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
          vbox(hbox(ppTyVarseq tyvarseq ^/^ ppTyCon tycon ^/^ below(text "=" ^/^ ppConBind conbind)) ^/^
          ppOpt (fn x => hbox(text "and" ^/^ ppDatBind x)) datbind_opt)

    and ppConBind (ConBind(I, _, vid, ty_opt, conbind_opt)) =
          vbox(hbox(ppVId vid ^/^ ppOpt (fn doc => text "of" ^/^ ppTy doc) ty_opt) ^/^
               ppOpt (fn x => hbox(text "|" ^/^ ppConBind x)) conbind_opt)

    and ppExBind (NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
          vbox(hbox(ppVId vid ^/^ ppOpt (fn doc => text "of" ^/^ ppTy doc) ty_opt) ^/^
          ppOpt (fn x => hbox(text "and" ^/^ ppExBind x)) exbind_opt)
      | ppExBind (EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
          vbox(hbox(ppVId vid ^/^ text "=" ^/^ ppLongVId longvid) ^/^ 
               ppOpt (fn x => hbox(text "and" ^/^ ppExBind x)) exbind_opt)

    (* Patterns *)

    and ppAtPat (WILDCARDAtPat(I)) = text "_"
      | ppAtPat (SCONAtPat(I, scon)) = ppSCon scon
      | ppAtPat (IDAtPat(I, _, longvid)) = ppLongVId longvid
      | ppAtPat (RECORDAtPat(I, patrow_opt)) = 
          if isPatTuple patrow_opt then
            paren(ppOpt ppPatRow patrow_opt)
          else brace(ppOpt ppPatRow patrow_opt)
      | ppAtPat (PARAtPat(I, pat)) = paren(ppPat pat)

    and ppPatRow (DOTSPatRow(I)) = text "..."
      | ppPatRow (FIELDPatRow(I, lab, pat, patrow_opt)) =
          (if isTupleLab lab then empty
          else ppLab lab ^/^ text "=") ^/^
          ppPat pat ^/^ 
          ppOpt (fn x => text "," ^/^ ppPatRow x) patrow_opt

    and ppPat (ATPat(I, atpat)) = ppAtPat atpat
      | ppPat (CONPat(I, _, longvid, atpat)) = ppLongVId longvid ^/^ ppAtPat atpat
      | ppPat (COLONPat(I, pat, ty)) = ppPat pat ^/^ text ":" ^/^ ppTy ty
      | ppPat (ASPat(I, _, vid, ty_opt, pat)) = 
          ppVId vid ^/^ ppOpt (fn x => text ":" ^/^ ppTy x) ty_opt ^/^
          text "as" ^/^ ppPat pat

    (* Type expressions *)

    and ppTy (VARTy(I, tyvar)) = ppTyVar tyvar
      | ppTy (RECORDTy(I, tyrow_opt, level)) = 
          if (isTyTuple tyrow_opt) then
            paren(ppOpt ppTyRow tyrow_opt) ^/^ ppLv level
          else brace(ppOpt ppTyRow tyrow_opt) ^/^ ppLv level
      | ppTy (CONTy(I, tyseq, longtycon, level)) =
          ppTyseq tyseq ^/^ ppLongTyCon longtycon ^/^ ppLv level
      | ppTy (ARROWTy(I, ty1, ty2, mode, level)) =
          paren(ppTy ty1 ^/^ text "->" ^/^ ppLv mode ^/^ ppTy ty2) ^/^ ppLv level
      | ppTy (PARTy(I, ty)) = paren(ppTy ty)

    and ppTyRow (TyRow(I, lab, ty, tyrow_opt)) =
          if (isTupleLab lab) then
            ppTy ty ^/^ ppOpt (fn x => text "*" ^/^ ppTyRow x) tyrow_opt
          else ppLab lab ^/^ text ":" ^/^ ppTy ty ^/^
               ppOpt (fn x => text "," ^/^ ppTyRow x) tyrow_opt

    and ppTyseq (Tyseq(I, tys)) = ppCommaList ppTy tys

    and ppTyVarseq (TyVarseq(I, tyvars)) = ppCommaList ppTyVar tyvars


    (* Module *)

    (* Structures *)

    fun ppStrDec (DECStrDec(I, dec)) = 
          hbox(ppDec dec)
      | ppStrDec (STRUCTUREStrDec(I, strbind)) =
          hbox(text "structure" ^/^ ppStrBind strbind)
      | ppStrDec (LOCALStrDec(I, strdec1, strdec2)) =
          vbox(nest(break ^^ text "local" ^^
                 nest(break ^^ below(ppStrDec strdec1)) ^/^
               text "in" ^/^
                 nest(break ^^ below(ppStrDec strdec2)) ^/^
               text "end"))
      | ppStrDec (EMPTYStrDec(I)) = empty
      | ppStrDec (SEQStrDec(I, strdec1, strdec2)) =
          vbox(ppStrDec strdec1 ^/^ ppStrDec strdec2)

    and ppStrBind (StrBind(I, strid, strexp, strbind_opt)) =
          vbox(hbox(ppStrId strid) ^/^ 
                  (*nest(break ^^ ppStrExp strexp) ^/^*)
               ppOpt ppStrBind strbind_opt)

    (* Top-level declarations *)

    and ppTopDec (STRDECTopDec(I, strdec, topdec_opt)) =
          vbox(ppStrDec strdec ^/^
               ppOpt (fn x => ppTopDec x) topdec_opt)
      | ppTopDec _ = empty


    (* Programs *)

    fun ppProgram (Program(I, topdec, program_opt)) =
      vbox(
        ppTopDec topdec ^/^
        ppOpt ppProgram program_opt ^/^
        text ""
      )

    fun printSML (Basis, program) =
        ( B := Basis;
          PrettyPrint.output(TextIO.stdOut, ppProgram program, 79);
          TextIO.flushOut TextIO.stdOut
        )

end;
