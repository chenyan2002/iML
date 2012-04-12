(*
 * Level variables
 * Standard ML type variables and sets and maps thereof
 *
 * Definition, Sections 2.4, 4.1, and 4.2
 *
 * Note:
 *  - Tvars can be annotated with an overloading class, to represent the
 *    type schemes of overloaded identifiers.
 *  - We wrap the overloading class into a reference so that TyVar is an eqtype.
 *  - Internally generated tyvars get names _'xxx, where xxx is a stamp number.
 *  - Tyvars generated from integers are mapped to 'a,'b,..,'z,'a1,'b1,..,'z1,
 *    'a2,...
 *)

structure LvVar :> LVVAR =
struct
    (* Import types *)

    (*type OverloadingClass = OverloadingClass.OverloadingClass*)

    (* Type [Sections 2.4 and 4.1]*)

    type LvVar = string


    (* Creation *)

    fun invent () = "_$" ^ Stamp.toString(Stamp.stamp())


    fun fromInt n =
	let
	    val c    = String.str(Char.chr(Char.ord #"a" + n mod 26))
	    val i    = n div 26
	    val name = "$" ^ (if i = 0 then c else c ^ Int.toString i)
	in
	    name
	end

    fun fromString s = s

    (* Attributes [Section 4.1] *)

    fun toString name = name

    (* Ordering *)

    fun compare(alpha1 : LvVar, alpha2 : LvVar) =
	String.compare(alpha1, alpha2)
end

structure LvVarSet = FinSetFn(type ord_key = LvVar.LvVar
			      val  compare = LvVar.compare)
structure LvVarMap = FinMapFn(type ord_key = LvVar.LvVar
			      val  compare = LvVar.compare);
