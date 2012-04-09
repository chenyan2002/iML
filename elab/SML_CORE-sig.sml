(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract core grammar
 *)

signature SML_CORE =
sig
    type VId        = IdsCore.VId
    type TyCon      = IdsCore.TyCon
    type StrId      = IdsCore.StrId
    type longVId    = IdsCore.longVId
    type longTyCon  = IdsCore.longTyCon
    type longStrId  = IdsCore.longStrId
    type TyVarseq   = GrammarCore.TyVarseq
    type Ty         = GrammarCore.Ty
    type Dec        = GrammarCore.Dec

    val ppVId :       VId -> PrettyPrint.doc
    val ppTyCon :     TyCon -> PrettyPrint.doc
    val ppStrId :     StrId -> PrettyPrint.doc
    val ppLongVId :   longVId -> PrettyPrint.doc
    val ppLongTyCon : longTyCon -> PrettyPrint.doc
    val ppLongStrId : longStrId -> PrettyPrint.doc
    val ppTyVarseq : TyVarseq -> PrettyPrint.doc

    val ppTy :        Ty -> PrettyPrint.doc

    val ppDec :       Dec -> PrettyPrint.doc
end;
