
structure Solver :> SOLVER = struct

  type var = LExp.var
  type checkpoint = int
  
  open LExp
  structure C = Constraint
  
  fun Array_mutate (arr, i, f) =
    Array.update (arr, i, f (Array.sub (arr, i)))

  (* As Array.modifyi, but only on elements from `lo' to `hi' - 1. *)
  fun Array_modifyi_range f (lo, hi) arr =
    if lo >= hi then ()
    else
        (Array.update (arr, lo, f (lo, Array.sub (arr, lo)));
         Array_modifyi_range f (lo + 1, hi) arr)

  (* As Array.modifyi, but only on elements in the given list of indices. *)
  fun Array_modifyi_list f indices arr =
    case indices of
      [] => ()
    | i :: rest => 
        (Array.update (arr, i, f (i, Array.sub (arr, i)));
         Array_modifyi_list f rest arr)

  (* As Array.appi, but only on elements from `lo' to `hi' - 1. *)
  fun Array_appi_range f (lo, hi) arr =
    if lo >= hi then ()
    else
        (f (lo, Array.sub (arr, lo));
         Array_appi_range f (lo + 1, hi) arr)

  (* As Array.appi, but only on elements in the given list of indices. *)
  fun Array_appi_list f indices arr =
    case indices of
      [] => ()
    | i :: rest => 
        (f (i, Array.sub (arr, i));
         Array_appi_list f rest arr)

  fun eqmember x [] = false
    | eqmember x (y::l) = (x = y) orelse eqmember x l

  fun elimDups xs =
      let fun add (x, xs) = if eqmember x xs then xs else x::xs
      in List.rev (foldl add [] xs) end

  fun assocLookup x [] = NONE
    | assocLookup x ((k,v)::l) = if x = k then SOME v else assocLookup x l

  fun incl x xs = case xs of
      [] => [x]
   | h::t => if h = x then h::t else h::(incl x t)

  exception Error of var list
  exception Failure of string

  datatype node =
    Node of {instance: lexp option, lo: var list, hi: var list, generalized: bool}

  type state = (int * node array) ref

  fun getLimit (ref (limit, _)) = limit

  fun getArray (ref (_, array)) = array


  fun setGeneralized c v =
    let fun set (Node{instance, lo, hi, generalized}) =
                 Node{instance= instance, lo= lo, hi= hi, generalized= true}
    in
      Array_mutate (getArray c, v, set)
    end


  fun new () = ref (0, Array.array (0, Node{instance=NONE, lo= [], hi= [], generalized= false}))
  

  fun checkpoint c =
     getLimit c
  

  fun subst c lexp = case lexp of
      S => S
    | C => C
    | Var v1 =>
        if v1 >= Array.length (getArray c) then
          Var v1
        else
          let val Node{instance= inst, ...} = Array.sub (getArray c, v1)
          in
             case inst of 
                 NONE => Var v1
               | SOME solution => solution
          end


  fun gather lexps =
    let fun gather1 acc S = acc
          | gather1 acc C = acc
          | gather1 acc (Var v) = v::acc
    in
      case lexps of
         [] => []
       | h::t => gather1 (gather t) h
    end


  fun expand c n =
      let val ref (limit, array) = c
          val limit = Int.max(limit, n + 1)
          val len = Array.length array
      in
          if n < Array.length array then
            c := (limit, array)
          else
            c := (limit, Array.tabulate (n * 2 + 1, fn i => if i < len then Array.sub (getArray c, i)
                                                            else Node{instance= NONE, lo= [], hi= [], generalized= false}))
      end

  
  fun instantiated c v expected =
      (expand c v;
       let val Node{instance= inst, ...} = Array.sub (getArray c, v)
       in
         case (inst, expected) of 
           (NONE, _) => false
         | (SOME solution, NONE) => true
         | (SOME solution, SOME expected) =>
              if solution = expected then true
              else
                raise (Failure "instantiate called with different solution")
       end)


  fun instantiate c v e =
      if instantiated c v (SOME e) then
        ()
      else
        (expand c v;
          let val Node{instance, lo, hi, generalized} = Array.sub (getArray c, v)
          in
              if generalized then
                  print ("instantiating generalized variable " ^ lexpToString (Var v) ^"?!\n")
              else ();
              Array.update (getArray c, v, 
                            Node{instance= SOME (* subst c *) e,
                                 lo= lo,
                                 hi= hi,
                                 generalized= generalized});
              
              case e of
                  S =>
                    (* Given lb <= v,  if v = S then lb = S *)
                      List.app (fn lb => instantiate c lb e) lo

                | C => 
                    (* Given v <= ub,  if v = C then ub = C *)
                      List.app (fn ub => instantiate c ub e) hi

                | _ => raise (Failure "non-constant level passed to instantiate")
         end)


  and add_eq c (lexp1, lexp2) = case (subst c lexp1, subst c lexp2) of
      (S, S) => ()
    | (C, C) => ()
    | (Var v1, S) => instantiate c v1 S
    | (S, Var v1) => instantiate c v1 S
    | (Var v1, C) => instantiate c v1 C
    | (C, Var v1) => instantiate c v1 C
    | (S, C) => raise Error (gather [lexp1, lexp2])
    | (C, S) => raise Error (gather [lexp1, lexp2])
    | (Var v1, Var v2) => if v1 = v2 then ()
                          else (add_leq c (lexp1, lexp2);
                                add_leq c (lexp2, lexp1))


  and add_var_leq c (v1, v2) =   (* add v1 <= v2 *) 
    (* assumes c already expanded *)
    (* assumes neither v1 nor v2 is solved  *)
    let val Node{instance= NONE, lo= lo1, hi= hi1, generalized= generalized1} = Array.sub (getArray c, v1)
        val Node{instance= NONE, lo= lo2, hi= hi2, generalized= generalized2} = Array.sub (getArray c, v2)
    in
        Array.update (getArray c, v1, Node{instance= NONE, lo= lo1, hi= incl v2 hi1, generalized= generalized1});
        Array.update (getArray c, v2, Node{instance= NONE, lo= incl v1 lo2, hi= hi2, generalized= generalized2})
    end


  and add_leq c (lexp1, lexp2) = case (subst c lexp1, subst c lexp2) of
      (S, _) => ()
    | (_, C) => ()
    | (C, S) => raise Error (gather [lexp1, lexp2])
    | (Var v1, S) => add_eq c (Var v1, S)
    | (C, Var v2) => add_eq c (Var v2, C)
    | (Var v1, Var v2) =>
         if v1 = v2 then ()
         else
           (expand c (Int.max(v1, v2));
            add_var_leq c (v1, v2))


   fun dump c =
    let fun dump_entry (v, b) =
       (print ("#" ^ Int.toString v);
        case b of
            Node{instance= lexp, lo= los, hi= his, generalized= generalized} =>
              (print (let in case generalized of
                          false => ":   "
                        | true => "-g-:"
                      end);
               let in case lexp of
                          NONE => ()
                        | SOME lexp => print (" = " ^ lexpToString lexp ^ ";")
               end;
               print (lexpsToString (List.map Var los) ^ " <= _ <= " ^ lexpsToString (List.map Var his));
               print "\n"));
    in
      print ("limit = " ^ Int.toString (getLimit c) ^ "\n");
      Array_appi_range dump_entry (0, getLimit c) (getArray c)
    end


  fun stateToConstraint' filterPredicate c =
    let fun entry (v, Node{instance= lexp, lo= los, hi= his, generalized= generalized}, acc) =
            if not (filterPredicate v) then acc
            else
              let val acc = 
                        let in case lexp of
                                    NONE => acc
                                  | SOME lexp =>
                                       C.EQ(Var v, lexp) :: acc
                        end

                  val acc =
                        let in case los of
                                   [] => acc
                                 | los => List.foldl (fn (lo_v, acc) => C.LE(Var lo_v, Var v) :: acc) acc los
                        end

                  val acc =
                        let in case his of
                                   [] => acc
                                 | his => List.foldl (fn (hi_v, acc) => C.LE(Var v, Var hi_v) :: acc) acc his
                        end
              in
                acc
              end
(*                val acc = 
                      let in case los of
                                 [] => (acc_string, sep)
                               | los => (acc_string ^ (if sep then " AND " else "")
                                         ^ List.map Var los 
             print (lexpsToString (List.map Var los) ^ " <= _ <= " ^ lexpsToString (List.map Var his));
             print "\n"));
*)
        val list = Array.foldri entry [] (getArray c)
        val culled_list = elimDups list
    in
        List.foldl C.AND C.TRUE (List.rev culled_list)
    end  

  fun stateToConstraint c =
    stateToConstraint' (fn _ => true) c


  fun generalize c point =
    let (* Does some variable connect to variables ``before'' `point'? *)
        fun connected visited v =
          if eqmember v visited then false
          else
            let val visited = v::visited
                val Node{lo= lo, hi= hi, ...} = Array.sub (getArray c, v)
                fun belowPoint v' = connected visited v'
            in
              v < point
              orelse
              List.exists belowPoint lo
              orelse
              List.exists belowPoint hi
            end

        val limit = getLimit c
        fun check v limit acc =
            if v = limit then acc
            else
                let val acc = (print (lexpToString (Var v)); if not (connected [] v) then
                                   (print " not connected\n";
                                    if not (instantiated c v NONE) then
                                        setGeneralized c v
                                    else ();
                                    v :: acc)
                              else
                                  (print " connected\n"; acc))
                in
                  check (v + 1) limit acc
                end
        
        (* Identify the variables ``after'' `point' that are NOT connected to variables ``before'' `point' *)
        val generalizables = check point limit []
        val generalizables = List.filter (fn v => not (instantiated c v NONE)) generalizables
        val constraint = stateToConstraint' (fn v => eqmember v generalizables) c
    in
      (generalizables, constraint)
    end

  val generalize = fn c => fn point =>
                     let val (vars, constraint) = generalize c point
                     in
                       print ("generalizing variables " ^ lexpsToString (List.map Var vars) ^ "\n");
                       print ("point was " ^ Int.toString point ^ "\n");
                       print ("constraint is " ^ Constraint.toString constraint ^ "\n");
                       (vars, constraint)
                     end


  fun copy c vs =
    let fun addVar v =
          let val new_v = getLimit c
              val _ = expand c new_v
          in
            (v, new_v)
          end

        val iso = List.map addVar vs
        
        fun copy1 (v, Node{instance, lo, hi, generalized}) =
          let val _ = if generalized then ()
                      else (print ("Solver.copy: attempt to copy " ^ lexpToString (Var v) ^ ", which is not generalized\n");
                            raise (Failure "Solver.copy"))
              val new_v = Option.valOf (assocLookup v iso)
              fun substitute v' = Option.getOpt (assocLookup v' iso, v')
          in
            Array.update (getArray c,
                          new_v,
                          Node{instance= instance (* closed *),
                               lo= List.map substitute lo,
                               hi= List.map substitute hi,
                               generalized= false})
          end
    in
      Array_appi_list copy1 vs (getArray c);
      List.map #2 iso
    end


  fun stabilize c =
    let fun entry (v, Node{instance, lo, hi, generalized}) =
            let val newInstance =
                    case (instance, generalized) of 
                        (_, true) => instance        (* if generalized, leave alone *)
                      | (SOME _, _) => instance      (* if already instantiated, leave alone *)
                      | (NONE, false) => SOME S      (* if not instantiated, and not generalized, force to be S *)
            in
              Node{instance= newInstance,
                   lo= lo,
                   hi= hi,
                   generalized= generalized}
            end
    in
      Array_modifyi_range entry (0, getLimit c) (getArray c)
    end


  fun stateToString c =
    C.toString (stateToConstraint c)

end 

