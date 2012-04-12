signature LEXP = sig

  (* Variables *)
  type var = int

  (* Level expressions *)
  datatype lexp = S | C | Var of var

  val lexpToString : lexp -> string
  val lexpsToString : lexp list -> string

  val gensym  : unit -> var
  
  val blast_r : int -> unit

end
