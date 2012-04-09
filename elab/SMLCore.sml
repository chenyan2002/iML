(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract core grammar
 *)

structure SMLCore : SML_CORE =
struct
    (* Import *)

    open GrammarCore
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^

    fun ppTyVar tyvar = text(TyVar.toString tyvar)

    fun ppDec (VALDec(I, tyvarseq, valbind)) =
          fbox(text "val " ^/^
               ppTyVarseq tyvarseq
              )
      | ppDec _ = empty

    and ppTyVarseq (TyVarseq(I, tyvars)) = 
        ppCommaList ppTyVar tyvars

end;
