(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core evaluation
 *
 * Definition, Section 6.7
 *
 * Notes:
 *   - State is passed as reference and modified via side effects. This way
 *     expanding out of the state and exception convention in the inference
 *     rules can be avoided (would really be a pain). Note that the state
 *     therefore never is returned.
 *   - Doing so, we can model the exception convention using exceptions.
 *)

signature EVAL_CORE =
sig
    (* Import types *)

    type Dec   = GrammarCore.Dec
    type Env   = DynamicObjectsCore.Env
    type State = DynamicObjectsCore.State

    (* Export *)

    val evalDec : State ref * Env * Dec -> Env
end;
