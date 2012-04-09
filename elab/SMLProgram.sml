(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract program grammar
 *)


structure SMLProgram : SML_PROGRAM =
struct
    (* Import *)

    open GrammarProgram
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^


    (* Programs *)

    fun ppProgram (Program(I, topdec, program_opt)) =
      vbox(
        SMLModule.ppTopDec topdec ^/^
        text "program_opt" ^/^
        text ""
      )

end;
