(*
 * (c) Andreas Rossberg 2007
 *
 * Printer for abstract module grammar
 *)

structure SMLModule : SML_MODULE =
struct
    (* Import *)

    open GrammarModule
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^

    (* Identifiers *)

    val ppSigID = text o SigId.toString
    val ppFunId = text o FunId.toString

    (* Structures *)



    fun ppStrDec (DECStrDec(I, dec)) = 
          hbox(SMLCore.ppDec dec)
      | ppStrDec (STRUCTUREStrDec(I, strbind)) =
          hbox(text "structure" ^/^ ppStrBind strbind)
      | ppStrDec (LOCALStrDec(I, strdec1, strdec2)) =
          vbox(nest(break ^^ text "local" ^^
                 nest(break ^^ below(ppStrDec strdec1)) ^/^
               text "in" ^/^
                 nest(break ^^ below(ppStrDec strdec2)) ^/^
               text "end"))
      | ppStrDec (EMPTYStrDec(I)) = empty
      | ppStrDec (SEQStrDec(I, strdec1, strdec2)) =
          vbox(ppStrDec strdec1 ^/^ ppStrDec strdec2)

    and ppStrBind (StrBind(I, strid, strexp, strbind_opt)) =
          vbox(hbox(SMLCore.ppStrId strid) ^/^ 
                  (*nest(break ^^ ppStrExp strexp) ^/^*)
               ppOpt ppStrBind strbind_opt)

    (* Top-level declarations *)

    and ppTopDec (STRDECTopDec(I, strdec, topdec_opt)) =
          vbox(ppStrDec strdec ^/^
               ppOpt (fn x => ppTopDec x) topdec_opt)
      | ppTopDec _ = empty



end;
