
signature FLOW_CORE =
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


    (* Export *)

    val elabDec :	bool -> Context * Dec -> Env
    val elabTy :	Context * Ty -> Type
    val tyvars :	TyVarseq -> TyVarSet * TyVar list
end;
