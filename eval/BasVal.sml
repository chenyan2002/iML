(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML basic values
 *
 * Definition, Section 6.4
 *)

structure BasVal :> BASVAL =
struct
    (* Import *)

    open DynamicObjectsCore


    (* Conversions *)

    fun toString b = b


    (* Application of basic values *)

    exception TypeError = Library.TypeError

    fun fromBool b = VId(VId.fromString(if b then "true" else "false"))

    fun APPLY("=", v) =
	(case Val.toPair v
	   of SOME vv => (fromBool(Val.equal vv) handle Domain =>
			  raise TypeError "equality type expected")
	    | NONE    => raise TypeError "pair expected"
	)
      | APPLY(b, v) = Library.APPLY(b, v)
end;
