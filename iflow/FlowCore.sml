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

    fun loopTopDec topdec =
      (AST.foreach {prog = topdec, 
                handleI = fn I => case ElabCore.peekType I of
                                NONE => ()
                              | SOME ty => setType(I, copyTy ty),
                handlePat = fn _ => ()};
       AST.foreach {prog = topdec,
                handleI = fn _ => (),
                handlePat = fn pat => case pat of
                                       COLONPat(I,pat,ty) => setType(I, getASTTy ty)
                                     | _ => ()}
      )



end;
