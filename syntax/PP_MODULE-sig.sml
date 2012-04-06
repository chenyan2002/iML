(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract module grammar
 *)

signature PP_MODULE =
sig
    type TopDec = GrammarModule.TopDec

    val ppTopDec : TextIO.outstream * int * TopDec -> unit
end;
