(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML identifiers
 *
 * Definition, Section 2.4
 *
 * Note:
 *   This is a generic functor to represent all kinds of identifiers (except
 *   labels and tyvars).
 *)


functor IdFn() :> ID =
struct
    (* Type [Section 2.4] *)

    type Id = string				(* [id] *)


    (* Creation *)

    fun invent()     = "_id" ^ Stamp.toString(Stamp.stamp())

    fun fromString s = s
    fun toString s   = s
    fun new s = s ^ "_" ^ Stamp.toString(Stamp.stamp())

    (* Ordering *)

    val compare = String.compare
end;
