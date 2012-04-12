signature CONSTRAINT = sig
  
  datatype constraint = 
      TRUE
    | AND of constraint * constraint
    | EQ of LExp.lexp * LExp.lexp
    | LE of LExp.lexp * LExp.lexp
   
  val toString : constraint -> string

end
