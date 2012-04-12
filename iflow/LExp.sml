
structure LExp :> LEXP = struct

  type var = int
  datatype lexp = S | C | Var of var

  val r : int ref = ref 0

  fun blast_r n = (r := n)

  fun gensym () = (!r before r := !r + 1)

  fun lexpToString lexp = case lexp of
     S => "S"
   | C => "C"
   | Var v => "#" ^ Int.toString v

  fun lexpsToString [] = "{}"
    | lexpsToString lexps = 
        let fun aux lexps = case lexps of
            [last] => lexpToString last ^ "}"
         | h::t => lexpToString h ^ ", " ^ aux t
        in
         "{" ^ aux lexps
        end

end
