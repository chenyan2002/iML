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

    fun loopTopDec topdec =
      foreach {prog = topdec, 
               handleI = fn I => (),
               handlePat = fn _ => ()}



end;
