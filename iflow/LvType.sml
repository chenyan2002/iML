
structure LvType =
struct
    (* Import *)

    type 'a LabMap	= 'a IdsCore.LabMap
    type 'a VIdMap	= 'a IdsCore.VIdMap
    type 'a TyConMap	= 'a IdsCore.TyConMap
    type 'a StrIdMap	= 'a IdsCore.StrIdMap

    (* Simple objects [Section 4.1 and Appendix E] *)

    type TyVar		= TyVar.TyVar				(* [alpha] *)
    type TyName		= TyName.TyName				(* [t] *)
    type IdStatus	= IdStatus.IdStatus			(* [is] *)

    (* Compound objects [Section 4.2] *)

    type RowVar		= {eq : bool, time : Stamp.stamp}	(* [r] *)

    datatype Type'	=					(* [tau] *)
	  TyVar		of TyVar
	| RowType	of RowType
	| FunType	of FunType
	| ConsType	of ConsType
	| Undetermined	of {stamp : Stamp.stamp, eq : bool, time : Stamp.stamp}
	| Overloaded	of OverloadingClass
	| Determined	of Type

    withtype Type	= Type' ref
    and      RowType	= Type' ref LabMap * RowVar option * Level.t ref	(* [rho] *)
    and      FunType	= Type' ref * Type' ref * Level.t ref * Level.t ref
    and      ConsType	= Type' ref list * TyName * Level.t ref

    type     TypeFcn	= TyVar list * Type			(* [theta] *)
    type     TypeScheme	= TyVar list * Type			(* [sigma] *)

end;
