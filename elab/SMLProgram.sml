(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract program grammar
 *)


structure SMLProgram : SML_PROGRAM =
struct
    (* Import *)

    open GrammarProgram
    open PPGrammar


    (* Programs *)

    fun ppProgram(out, i, Program(I, topdec, program_opt)) =
	    ppElem(out, i, "Program", I,
		   [sub SMLModule.ppTopDec topdec, subo ppProgram program_opt])
end;
