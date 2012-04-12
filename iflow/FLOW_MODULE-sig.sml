
signature FLOW_MODULE =
sig
    (* Import types *)

    type TopDec = GrammarModule.TopDec
    type Basis  = StaticObjectsModule.Basis

    (* Export *)

    val elabTopDec : Basis * TopDec -> Basis
end;
