signature SOLVER = sig

  type var = LExp.var

  exception Error of var list
  exception Failure of string
  type state   (* WARNING: stateful! *)
  type checkpoint  (* tied to state *)
  
  val new  : unit -> state
  
  (* subst c e1 --- Extract the known variables (variables constrained to be <= S, or >= C)
                      from c, and substitute in e1 accordingly *)
  val subst  : state -> LExp.lexp -> LExp.lexp
  
  (* gather es = [v such that Var(v) in es] *)
  val gather  : LExp.lexp list -> var list
  
  (* add_eq c (e1, e2) --- Add the state (e1 = e2); raises Error if inconsistent *)
                        (* (Equivalent to (add_leq c (e1, e2); add_leq c (e2, e1))) *)
  val add_eq  : state -> LExp.lexp * LExp.lexp -> unit

  (* add_leq c (e1, e2) --- Add the state (e1 <= e2); raises Error if inconsistent *)
  val add_leq  : state -> LExp.lexp * LExp.lexp -> unit
  
  (* checkpoint c --- Return a checkpoint that can be passed to `generalize' *)
  val checkpoint  : state -> checkpoint

  (* generalize c point ---
     Let state[D] be the part of the state that does NOT involve variables that
       existed at `point'.  Return the set of variables in state[D],
       and the constraint on state[D].

     Also marks variables in state[D] as ``generalized'',
     so `stabilize' can know not to instantiate them.
   *)
  val generalize : state -> checkpoint -> (var list * Constraint.constraint)
  
  (* copy c vs = new_vs  --- Create new variables `new_vs' with constraints isomorphic to `vs'.
   * --- PRECONDITION: All variables in `vs' must have been generalized.
   * --- Example: Given x1, x2 with x1 <= x2,  copy [x1, x2] creates x1', x2' with x1' <= x2',
   * ---          and returns [x1', x2'].
   *)
  val copy : state -> var list -> var list
  
  (* forced stabilization --- Instantiates to S all uninstantiated, nongeneralized variables. *)
  val stabilize : state -> unit
      
  (* stateToString c  =  a (relatively) economical rendering of c --- SEE ALSO `dump' *)
  val stateToString : state -> string
  
  (* dump c --- Dump the internal representation of c --- SEE ALSO `stateToString' *)
  val dump  : state -> unit
  
end 
