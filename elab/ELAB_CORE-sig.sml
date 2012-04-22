(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core elaboration
 *
 * Definition, Sections 4.10, 4.11, 4.6, 4.7, 2.9
 *
 * Notes:
 *   - Elaboration also checks the further restrictions [Section 4.11].
 *   - To implement the 3rd restriction in 4.11 elabDec is passed an
 *     additional boolean argument to recognise being on the toplevel.
 *)

signature ELAB_CORE =
sig
    (* Import *)

    type VId		= IdsCore.VId
    type TyVar		= IdsCore.TyVar

    type Dec		= GrammarCore.Dec
    type Ty		= GrammarCore.Ty
    type TyVarseq	= GrammarCore.TyVarseq

    type TyVarSet	= StaticObjectsCore.TyVarSet
    type Type		= StaticObjectsCore.Type
    type Env		= StaticObjectsCore.Env
    type Context	= StaticObjectsCore.Context

    type Info           = GrammarCore.Info


    (* Export *)

    val elabDec :	bool -> Context * Dec -> Env
    val elabTy :	Context * Ty -> Type
    val tyvars :	TyVarseq -> TyVarSet * TyVar list

    val getType   : Info -> Type
    val setType   : Info * Type -> unit
    val peekType  : Info -> Type option
    val getScheme : Info -> StaticObjectsCore.TypeScheme
end;
