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

    (*type Id = string*)				(* [id] *)
    datatype Id = V of {
             name : string,
             suffix : string
           }

    (* Creation *)

    (*fun invent()     = "_id" ^ Stamp.toString(Stamp.stamp())*)
    fun invent() = V{name = "_id",
                     suffix = Stamp.toString(Stamp.stamp())}

    fun fromString s = V{name = s, suffix = ""}
    fun toString (V{name,suffix}) = name ^ (if suffix="" then "" else "_" ^ suffix)
    fun new (V{name,suffix}) = V{name = name,
			       suffix = if suffix="" then Stamp.toString(Stamp.stamp()) else suffix}
    fun name (V{name,...}) = name
    fun suffix (V{suffix,...}) = suffix

    (* Ordering *)

    fun compare (a, b) = String.compare (toString a, toString b)
end;
