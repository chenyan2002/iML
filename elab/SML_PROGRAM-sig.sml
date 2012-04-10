(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract program grammar
 *)

signature SML_PROGRAM =
sig
    type Program = GrammarProgram.Program

    val printSML : StaticObjectsModule.Basis * Program -> unit
end;
