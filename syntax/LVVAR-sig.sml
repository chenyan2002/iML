(*
 Level variable. The definition is similar to TyVar
*)

signature LVVAR =
sig
    (* Import types *)

    (*type OverloadingClass = OverloadingClass.OverloadingClass*)

    (* Type [Sections 2.4 and 4.1]*)

    eqtype LvVar			(* [alpha] or [tyvar] *)

    (* Operations *)

    val invent :		bool -> LvVar
    val fromInt :		bool -> int -> LvVar
    val fromString :		string -> LvVar
    (*val fromOverloadingClass :	string * OverloadingClass -> LvVar*)
    val toString :		LvVar -> string

    val admitsEquality :	LvVar -> bool
    (*val overloadingClass :	LvVar -> OverloadingClass option*)

    val compare :		LvVar * LvVar -> order
end;
