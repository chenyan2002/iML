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
    val peekType = ElabCore.peekType
    val getScheme = ElabCore.getScheme
    val getRefer = ElabCore.getRefer
    val peekRefer = ElabCore.peekRefer
    fun getReferTy I = case peekRefer I of
                         SOME I => getType(I)
                       | NONE => getType(I)

    val error = fn (str,tau) => (PrettyPrint.output (TextIO.stdOut, PPType.ppType tau, 79);
                                TextIO.flushOut TextIO.stdOut;
                                error(Source.nowhere, "\n"^str))

    fun getLv tau =
      case !tau of
        RowType (_,_,lv) => lv
      | FunType (_,_,_,lv) => lv
      | ConsType (_,_,lv) => lv
      | Determined tau => getLv tau
      | _ => error ("getLv: no level info", tau)
              
             
    fun copyTy ty =
      let
        val copy_ty =
            case !ty of
              RowType (lab,ty,lv) => RowType (lab,ty,ref (!lv)) (* TODO *)
            | FunType (a,b,mode,lv) => FunType (copyTy a,copyTy b,ref (!mode),ref(!lv))
            | ConsType (tys,name,lv) => ConsType (map copyTy tys,name,ref(!lv))
            | Determined ty => Determined (copyTy ty)
            | t => t
        val ty = ref copy_ty
      in
        ty
      end

    fun getASTTy ty =
      case ty of
        VARTy(I,tyvar) => Type.fromTyVar tyvar
      | RECORDTy(I,tyrow_opt,lv) => 
        let
          val rho = case tyrow_opt of
                      NONE => Type.emptyRow
                    | SOME tyrow => getTyRow tyrow
          val (_,_,level) = rho
          val _ = level := lv
          val tau = Type.fromRowType rho
        in tau end
      | CONTy(I, tyseq, longtycon, lv) => 
        let
          val tyname = Type.tyname (getType I)
          val Tyseq(I',tys) = tyseq
          val taus = List.map getASTTy tys
        in Type.fromConsType (taus, tyname, ref lv) end
      | ARROWTy(I,ty,ty',mode,lv) => 
        let
          val tau1 = getASTTy ty
          val tau2 = getASTTy ty'
        in Type.fromFunType(tau1,tau2,ref mode,ref lv) end
      | PARTy(I,ty) => getASTTy ty
    and getTyRow (TyRow(I,lab,ty,tyrow_opt)) =
        let
          val tau = getASTTy ty
          val rho = case tyrow_opt of
                      NONE => Type.emptyRow
                    | SOME tyrow => getTyRow tyrow
        in Type.insertRow(rho,lab,tau) end

    fun loopOpt f opt = case opt of
                          NONE => ()
                        | SOME opt => f opt

    (* Core *)

   (* Expressions *)

    fun loopAtExp atexp =
      let
        val tau = getType(infoAtExp atexp)
      in
        case atexp of
          SCONAtExp(I, scon) => (getLv tau) := Level.Stable
        | IDAtExp(I, _, longvid) => (setType(I,getReferTy I))
        | RECORDAtExp(I, exprow_opt) => loopOpt loopExpRow exprow_opt 
        | LETAtExp(I, dec, exp) => (
          loopDec dec; 
          loopExp exp)
        | PARAtExp(I, exp) => loopExp exp
      end

    and loopExpRow (ExpRow(I, lab, exp, exprow_opt)) =
           loopOpt loopExpRow exprow_opt

    and loopExp exp =
         case exp of
           (ATExp(I, atexp)) => loopAtExp atexp
         | (APPExp(I, exp, atexp)) => (loopExp exp; loopAtExp atexp)
         | (COLONExp(I, exp, ty)) => loopExp exp
         | (HANDLEExp(I, exp, match)) => (loopExp exp; loopMatch match)
         | (RAISEExp(I, exp)) => loopExp exp
         | (FNExp(I, match)) => loopMatch match

    (* Matches *)

    and loopMatch (Match(I, mrule, match_opt)) = 
         (loopMrule mrule; 
          loopOpt loopMatch match_opt)
    and loopMrule (Mrule(I, pat, exp)) = 
         (loopPat pat;
          loopExp exp)

    (* Declarations *)

    and loopDec dec =
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
         | (SEQDec(I, dec1, dec2)) => (loopDec dec1; loopDec dec2)

    and loopValBind (PLAINValBind(I, pat, exp, valbind_opt)) =
          (loopPat pat; loopExp exp; loopOpt loopValBind valbind_opt;
           setType(I, getType(infoPat pat))
          )
      | loopValBind (RECValBind(I, valbind)) = (loopValBind valbind)

    and loopTypBind (TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
          (loopOpt loopTypBind typbind_opt)
          
    and loopDatBind (DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
          (loopOpt loopDatBind datbind_opt)

    and loopConBind (ConBind(I, _, vid, ty_opt, conbind_opt)) =
          (loopOpt loopConBind conbind_opt)

    and loopExBind (NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
          (loopOpt loopExBind exbind_opt)
      | loopExBind (EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
          (loopOpt loopExBind exbind_opt)

    (* Patterns *)

    and loopAtPat atpat =
         case atpat of
           (WILDCARDAtPat(I)) => ()
         | (SCONAtPat(I, scon)) => ()
         | (IDAtPat(I, _, longvid)) => ()
         | (RECORDAtPat(I, patrow_opt)) => 
             loopOpt loopPatRow patrow_opt
         | (PARAtPat(I, pat)) => loopPat pat
                                
    and loopPatRow (DOTSPatRow(I)) = ()
      | loopPatRow (FIELDPatRow(I, lab, pat, patrow_opt)) =
           (loopPat pat;
            loopOpt loopPatRow patrow_opt)

    and loopPat pat =
         case pat of 
           (ATPat(I, atpat)) => loopAtPat atpat
         | (CONPat(I, _, longvid, atpat)) => loopAtPat atpat
         | (COLONPat(I, pat, ty)) => 
             (loopPat pat;
              setType(I, getASTTy ty))
         | (ASPat(I, _, vid, ty_opt, pat)) => loopPat pat

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


    fun processTopDec topdec =
      (AST.foreach {prog = topdec, 
                handleI = fn I => case ElabCore.peekType I of
                                NONE => ()
                              | SOME ty => setType(I, copyTy ty),
                handlePat = fn _ => ()};
       loopTopDec topdec
      )



end;
