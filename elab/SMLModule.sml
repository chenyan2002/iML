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

    fun ppTopDec topdec =
      case topdec of
        STRDECTopDec(I, strdec, topdec_opt) => vbox( ppStrDec strdec ^/^
                                                    ppOpt ppTopDec topdec_opt)
      | _ => empty

    and ppStrDec strdec = 
        case strdec of
          DECStrDec(I, dec) => SMLCore.ppDec dec
        | _ => empty

end;
