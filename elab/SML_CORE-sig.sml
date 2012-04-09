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

    val ppVId :       TextIO.outstream * int * VId -> unit
    val ppTyCon :     TextIO.outstream * int * TyCon -> unit
    val ppStrId :     TextIO.outstream * int * StrId -> unit
    val ppLongVId :   TextIO.outstream * int * longVId -> unit
    val ppLongTyCon : TextIO.outstream * int * longTyCon -> unit
    val ppLongStrId : TextIO.outstream * int * longStrId -> unit
    val ppTyVarseq :  TextIO.outstream * int * TyVarseq -> unit

    val ppTy :        TextIO.outstream * int * Ty -> unit
    val ppDec :       TextIO.outstream * int * Dec -> unit
end;
