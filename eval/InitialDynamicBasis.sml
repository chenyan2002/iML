(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML initial dynamic basis
 *
 * Definition, Appendix D
 *
 * Note:
 *     The Definition does not specify what the initial state has to contain.
 *     This is a bug as it must at least contain the exception names Match
 *     and Bind. We put the state associated with the initial basis in
 *     here, too.
 *)

structure InitialDynamicBasis : INITIAL_DYNAMIC_BASIS =
struct
    (* Import *)

    type Basis = DynamicObjectsModule.Basis
    type State = DynamicObjectsCore.State


    (* Enviornments *)

    val F0 = FunIdMap.empty
    val G0 = SigIdMap.empty
    val E0 = InitialDynamicEnv.E0

    val B0 = (F0,G0,E0)


    (* Associated state *)

    val s0 = InitialDynamicEnv.s0
end;
