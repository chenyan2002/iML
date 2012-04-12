structure Test = struct
    open LExp
    open Constraint
    open Solver

    fun dump' c = print (stateToString c ^ "\n\n")

    val c = new()
    val _ = blast_r 10
    val _ = (dump' c; print "\n--------a\n")
    val _ = add_eq c (Var 0, Var 1)
    val _ = (dump' c; print "\n--------b\n")
    val _ = add_eq c (Var 1, S)
    val _ = (dump' c; print "\n--------c\n")
    val _ = add_leq c (S, Var 3)
    val _ = (dump' c; print "\n--------d\n")
    val _ = add_leq c (C, Var 2)
    val _ = (dump' c; print "\n--------e\n")
    val _ = add_leq c (Var 3, Var 4)
    val _ = (dump' c; print "\n--------f1\n")
    val _ = add_leq c (Var 4, Var 3)
    val _ = (dump' c; print "\n--------f2\n")

    val _ = add_leq c (Var 5, Var 6)
    val _ = add_leq c (Var 6, Var 7)
    val _ = add_leq c (Var 8, Var 9)
    val _ = (dump' c; print "\n--------567_89\n")

    val _ = add_leq c (Var 7, Var 8)
    val _ = add_leq c (Var 6, Var 66)
    val _ = add_leq c (Var 66, Var 67)
    val _ = add_leq c (Var 66, Var 68)
    val _ = (dump' c; print "\n--------56789\n")

    val _ = add_leq c (C, Var 6)
    val _ = (dump' c; print "\n--------56789 + 6=C\n")

    (* val _ = solve c *)
    (* val _ = (dump' c; print "\n--------z\n") *)

     val _ = print "\n\n\n\n\n\n\n\n\n\n\n"

     val c = new()
     val _ = add_eq c (Var 0, Var 1)
     val point = checkpoint c
     val _ = add_eq c (Var 2, Var 3)
     val _ = add_eq c (Var 4, Var 5)
     val _ = add_eq c (Var 6, Var 7)
     val _ = add_leq c (Var 1, Var 5)
     val _ = add_leq c (C, Var 4)

     val _ = (print "1>>>>> "; dump c; print "\n")
     val _ = add_eq c (Var 7, S)
     val (gens, constraint) = generalize c point
     val _ = (print "2>>>>> "; dump c; print "\n")
     val _ = stabilize c
     val _ = (print "3>>>>> "; dump c; print "\n")

     val vs' = copy c [2,3]
     val _ = print ("vs' = " ^ lexpsToString (List.map Var vs') ^ "\n")
     val _ = (print "4>>>>> "; dump c; print "\n")

end (* structure Test *)
