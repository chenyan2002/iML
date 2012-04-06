(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML modules derived forms
 *
 * Definition, Appendix A
 *
 * Notes:
 * - A phrase named SynDesc has been added to factorize type synonym
 *   specifications.
 * - Similarly, a phrase named TyReaDesc has been added to factorize type
 *   realisation signature expressions.
 * - The structure sharing derived form is missing since it cannot be resolved
 *   syntactically. It has been moved to the bare grammar.
 *)

signature DERIVED_FORMS_MODULE =
sig
    (* Import *)

    type Info       = GrammarModule.Info

    type VId        = GrammarCore.VId
    type TyCon      = GrammarCore.TyCon
    type StrId      = GrammarCore.StrId
    type SigId      = GrammarModule.SigId
    type FunId      = GrammarModule.FunId
    type longTyCon  = GrammarCore.longTyCon

    type Ty         = GrammarCore.Ty
    type TyVarseq   = GrammarCore.TyVarseq

    type StrExp     = GrammarModule.StrExp
    type StrDec     = GrammarModule.StrDec
    type StrBind    = GrammarModule.StrBind
    type SigExp     = GrammarModule.SigExp
    type TyReaDesc  = (Info * TyVarseq * longTyCon * Ty) list
    type Spec       = GrammarModule.Spec
    type SynDesc    = (Info * TyVarseq * TyCon * Ty) list
    type FunBind    = GrammarModule.FunBind


    (* Structure Bindings [Figure 18] *)

    val TRANSStrBind :		Info * StrId * SigExp option * StrExp
				     * StrBind option -> StrBind
    val SEALStrBind :		Info * StrId * SigExp * StrExp
				     * StrBind option -> StrBind

    (* Structure Expressions [Figure 18] *)

    val APPDECStrExp :		Info * FunId * StrDec -> StrExp

    (* Functor Bindings [Figure 18] *)

    val TRANSFunBind :		Info * FunId * StrId * SigExp * SigExp option
				     * StrExp * FunBind option -> FunBind
    val SEALFunBind :		Info * FunId * StrId * SigExp * SigExp
				     * StrExp * FunBind option -> FunBind
    val TRANSSPECFunBind :	Info * FunId * Spec * SigExp option
				     * StrExp * FunBind option -> FunBind
    val SEALSPECFunBind :	Info * FunId * Spec * SigExp
				     * StrExp * FunBind option -> FunBind

    (* Specifications [Figure 19] *)

    val SYNSpec :		Info * SynDesc -> Spec
    val INCLUDEMULTISpec :	Info * SigId list -> Spec

    val SynDesc :		Info * TyVarseq * TyCon * Ty
				     * SynDesc option -> SynDesc

    (* Signature Expressions [Figure 19] *)

    val WHERETYPESigExp :	Info * SigExp * TyReaDesc -> SigExp

    val TyReaDesc :		Info * TyVarseq * longTyCon * Ty
				     * TyReaDesc option -> TyReaDesc
end;
