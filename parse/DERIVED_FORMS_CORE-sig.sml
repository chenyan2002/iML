(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core derived forms
 *
 * Definition, Section 2.7 and Appendix A
 *
 * Note:
 *   Two phrases named Fmatch and Fmrule have been added to factorize FvalBind.
 *)

signature DERIVED_FORMS_CORE =
sig
    (* Import *)

    type Info      = GrammarCore.Info

    type Lab       = GrammarCore.Lab
    type VId       = GrammarCore.VId

    type Op        = GrammarCore.Op
    type AtExp     = GrammarCore.AtExp
    type AppExp    = GrammarCore.AtExp list
    type InfExp    = GrammarCore.Exp
    type Exp       = GrammarCore.Exp
    type Match     = GrammarCore.Match
    type Mrule     = GrammarCore.Mrule
    type Dec       = GrammarCore.Dec
    type ValBind   = GrammarCore.ValBind
    type FvalBind  = GrammarCore.ValBind
    type Fmatch    = GrammarCore.Match * VId * int
    type Fmrule    = GrammarCore.Mrule * VId * int
    type TypBind   = GrammarCore.TypBind
    type DatBind   = GrammarCore.DatBind
    type AtPat     = GrammarCore.AtPat
    type PatRow    = GrammarCore.PatRow
    type Pat       = GrammarCore.Pat
    type Ty        = GrammarCore.Ty
    type TyVarseq  = GrammarCore.TyVarseq


    (* Expressions [Figure 15] *)

    val UNITAtExp :	Info					-> AtExp
    val TUPLEAtExp :	Info * Exp list				-> AtExp
    val HASHAtExp :	Info * Lab				-> AtExp
    val CASEExp :	Info * Exp * Match			-> Exp
    val IFExp :		Info * Exp * Exp * Exp			-> Exp
    val ANDALSOExp :	Info * Exp * Exp			-> Exp
    val ORELSEExp :	Info * Exp * Exp			-> Exp
    val SEQAtExp :	Info * Exp list				-> AtExp
    val LETAtExp :	Info * Dec * Exp list			-> AtExp
    val WHILEExp :	Info * Exp * Exp			-> Exp
    val LISTAtExp :	Info * Exp list				-> AtExp

    (* Patterns [Figure 16] *)

    val UNITAtPat :	Info					-> AtPat
    val TUPLEAtPat :	Info * Pat list				-> AtPat
    val LISTAtPat :	Info * Pat list				-> AtPat

    val IDPatRow :	Info * VId * Ty option * Pat option * PatRow option
								-> PatRow
    (* Types [Figure 16] *)

    val TUPLETy :	Info * Ty list				-> Ty

    (* Function-value bindings [Figure 17] *)

    val FvalBind :	Info * Fmatch * FvalBind option		-> FvalBind
    val Fmatch :	Info * Fmrule * Fmatch option		-> Fmatch
    val Fmrule :	Info * Op * VId * AtPat list * Ty option * Exp -> Fmrule

    (* Declarations [Figure 17] *)

    val FUNDec :	Info * TyVarseq * FvalBind		-> Dec
    val DATATYPEDec :	Info * DatBind * TypBind option		-> Dec
    val ABSTYPEDec :	Info * DatBind * TypBind option * Dec	-> Dec
end;
