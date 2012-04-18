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

    val invent :		unit -> LvVar
    val fromInt :		int -> LvVar
    val fromString :		string -> LvVar
    (*val fromOverloadingClass :	string * OverloadingClass -> LvVar*)
    val toString :		LvVar -> string
    val new : LvVar -> LvVar
    val name : LvVar -> string
    val suffix : LvVar -> string

    val compare :		LvVar * LvVar -> order
end;
