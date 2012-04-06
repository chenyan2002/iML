(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML modules elaboration
 *
 * Definition, Sections 5.7 and 3.5
 *)

signature ELAB_MODULE =
sig
    (* Import types *)

    type TopDec = GrammarModule.TopDec
    type Basis  = StaticObjectsModule.Basis

    (* Export *)

    val elabTopDec : Basis * TopDec -> Basis
end;
