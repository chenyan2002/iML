
structure Constraint :> CONSTRAINT = struct

  val lexpToString = LExp.lexpToString

  datatype constraint = 
      TRUE
    | AND of constraint * constraint
    | EQ of LExp.lexp * LExp.lexp
    | LE of LExp.lexp * LExp.lexp

  fun toString p = case p of
      TRUE => "TRUE"
    | AND(p1, p2) => toString p1 ^ " AND " ^ toString p2
    | EQ(e1, e2) => "(" ^ lexpToString e1 ^ " = " ^ lexpToString e2 ^ ")"
    | LE(e1, e2) =>  "(" ^ lexpToString e1 ^ " <= " ^ lexpToString e2 ^ ")"


end
