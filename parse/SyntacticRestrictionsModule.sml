(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML syntactic restrictions for modules
 *
 * Definition, Section 3.5
 *)

structure SyntacticRestrictionsModule : SYNTACTIC_RESTRICTIONS_MODULE =
struct
    (* Import *)

    open GrammarModule
    open BindingObjectsModule
    open Error


    (* Helpers for basis modification *)

    val empty  = BindingBasis.plus
    val plus   = BindingBasis.plus
    val plusG  = BindingBasis.plusG
    val plusF  = BindingBasis.plusF
    val plusE  = BindingBasis.plusE
    val plusSE = BindingBasis.plusSE

    infix plus plusG plusF plusE plusSE


    (* Inference rules [Section 5.7] *)


    (* Structure Expressions *)

    fun checkStrExp(B, STRUCTStrExp(I, strdec)) =
	let
	    val E = checkStrDec(B, strdec)
	in
	    E
	end

      | checkStrExp(B, IDStrExp(I, longstrid)) =
	let
	    val E = case BindingBasis.findLongStrId(B, longstrid)
		      of SOME E => E
		       | NONE   => BindingEnv.empty (* actually an error *)
	in
	    E
	end

      | checkStrExp(B, COLONStrExp(I, strexp, sigexp)) =
	let
	    val E1 = checkStrExp(B, strexp)
	    val E2 = checkSigExp(B, sigexp)
	in
	    E2
	end

      | checkStrExp(B, SEALStrExp(I, strexp, sigexp)) =
	let
	    val E1 = checkStrExp(B, strexp)
	    val E2 = checkSigExp(B, sigexp)
	in
	    E2
	end

      | checkStrExp(B, APPStrExp(I, funid, strexp)) =
	let
	    val E1 = checkStrExp(B, strexp)
	    val E2 = case BindingBasis.findFunId(B, funid)
		       of SOME E => E
		        | NONE   => BindingEnv.empty (* actually an error *)
	in
	    E2
	end

      | checkStrExp(B, LETStrExp(I, strdec, strexp)) =
	let
	    val E1 = checkStrDec(B, strdec)
	    val E2 = checkStrExp(B plusE E1, strexp)
	in
	    E2
	end


    (* Structure-level Declarations *)

    and checkStrDec(B, DECStrDec(I, dec)) =
	let
	    val E = SyntacticRestrictionsCore.checkDec(BindingBasis.Cof B, dec)
	in
	    E
	end

      | checkStrDec(B, STRUCTUREStrDec(I, strbind)) =
	let
	    val SE = checkStrBind(B, strbind)
	in
	    BindingEnv.fromSE SE
	end

      | checkStrDec(B, LOCALStrDec(I, strdec1, strdec2)) =
	let
	    val E1 = checkStrDec(B, strdec1)
	    val E2 = checkStrDec(B plusE E1, strdec2)
	in
	    E2
	end

      | checkStrDec(B, EMPTYStrDec(I)) =
	    BindingEnv.empty

      | checkStrDec(B, SEQStrDec(I, strdec1, strdec2)) =
	let
	    val E1 = checkStrDec(B, strdec1)
	    val E2 = checkStrDec(B plusE E1, strdec2)
	in
	    BindingEnv.plus(E1, E2)
	end


    (* Structure Bindings *)

    and checkStrBind(B, StrBind(I, strid, strexp, strbind_opt)) =
	let
	    val E  = checkStrExp(B, strexp)
	    val SE = case strbind_opt
		       of NONE         => StrIdMap.empty
		        | SOME strbind => checkStrBind(B, strbind)
	in
	    if StrIdMap.inDomain(SE, strid) then
		(* [Section 3.5, 1st bullet] *)
		errorStrId(I, "duplicate structure identifier ", strid)
	    else
		StrIdMap.insert(SE, strid, E)
	end


    (* Signature Expressions *)

    and checkSigExp(B, SIGSigExp(I, spec)) =
	let
	    val E = checkSpec(B, spec)
	in
	    E
	end

      | checkSigExp(B, IDSigExp(I, sigid)) =
	let
	    val E = case BindingBasis.findSigId(B, sigid)
		      of SOME E => E
		       | NONE   => BindingEnv.empty (* actually an error *)
	in
	    E
	end

      | checkSigExp(B, WHERETYPESigExp(I, sigexp, tyvarseq, longtycon, ty)) =
	let
	    val E  = checkSigExp(B, sigexp)
	    val U1 = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val U2 = SyntacticRestrictionsCore.checkTy ty
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* [Section 3.5, 4th bullet] *)
		error(I, "free type variables in type realisation")
	    else
		E
	end


    (* Signature Declarations *)

    and checkSigDec(B, SigDec(I, sigbind)) =
	let
	    val G = checkSigBind(B, sigbind)
	in
	    G
	end


    (* Signature Bindings *)

    and checkSigBind(B, SigBind(I, sigid, sigexp, sigbind_opt)) =
	let
	    val E = checkSigExp(B, sigexp)
	    val G = case sigbind_opt
		      of NONE         => SigIdMap.empty
		       | SOME sigbind => checkSigBind(B, sigbind)
	in
	    if SigIdMap.inDomain(G, sigid) then
		(* [Section 3.5, 1st bullet] *)
		errorSigId(I, "duplicate signature identifier ", sigid)
	    else
		SigIdMap.insert(G, sigid, E)
	end


    (* Specifications *)

    and checkSpec(B, VALSpec(I, valdesc)) =
	let
	    val VE = checkValDesc valdesc
	in
	    BindingEnv.fromVE VE
	end

      | checkSpec(B, TYPESpec(I, typdesc)) =
	let
	    val TE = checkTypDesc typdesc
	in
	    BindingEnv.fromTE TE
	end

      | checkSpec(B, EQTYPESpec(I, typdesc)) =
	let
	    val TE = checkTypDesc typdesc
	in
	    BindingEnv.fromTE TE
	end

      | checkSpec(B, DATATYPESpec(I, datdesc)) =
	let
	    val (VE,TE) = checkDatDesc datdesc
	in
	    BindingEnv.fromVEandTE(VE,TE)
	end

      | checkSpec(B, DATATYPE2Spec(I, tycon, longtycon)) =
	let
	    val VE = case BindingBasis.findLongTyCon(B, longtycon)
		       of SOME VE => VE
			| NONE    => VIdMap.empty (* actually an error *)
	    val TE = TyConMap.singleton(tycon, VE)
	in
	    BindingEnv.fromVEandTE(VE,TE)
	end

      | checkSpec(B, EXCEPTIONSpec(I, exdesc)) =
	let
	    val VE = checkExDesc exdesc
	in
	    BindingEnv.fromVE VE
	end

      | checkSpec(B, STRUCTURESpec(I, strdesc)) =
	let
	    val SE = checkStrDesc(B, strdesc)
	in
	    BindingEnv.fromSE SE
	end

      | checkSpec(B, INCLUDESpec(I, sigexp)) =
	let
	    val E = checkSigExp(B, sigexp)
	in
	    E
	end

      | checkSpec(B, EMPTYSpec(I)) =
	    BindingEnv.empty

      | checkSpec(B, SEQSpec(I, spec1, spec2)) =
	let
	    val E1 = checkSpec(B, spec1)
	    val E2 = checkSpec(B plusE E1, spec2)
	in
	    BindingEnv.plus(E1, E2)
	end

      | checkSpec(B, SHARINGTYPESpec(I, spec, longtycons)) =
	let
	    val E = checkSpec(B, spec)
	in
	    E
	end

      | checkSpec(B, SHARINGSpec(I, spec, longstrids)) =
	(* [Appendix A] *)
	let
	    val E = checkSpec(B, spec)
	in
	    E
	end


    (* Value Descriptions *)

    and checkValDesc(ValDesc(I, vid, ty, valdesc_opt)) =
	let
	    val U  = SyntacticRestrictionsCore.checkTy ty
	    val VE = case valdesc_opt
		       of NONE         => VIdMap.empty
			| SOME valdesc => checkValDesc valdesc
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate variable ", vid)
	    else if not(SyntacticRestrictionsCore.validBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specification of identifier ", vid)
	    else
		VIdMap.insert(VE, vid, IdStatus.v)
	end


    (* Type Descriptions *)

    and checkTypDesc(TypDesc(I, tyvarseq, tycon, typdesc_opt)) =
	let
	    val U  = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val TE = case typdesc_opt
		       of NONE         => TyConMap.empty
			| SOME typdesc => checkTypDesc typdesc
	in
	    if TyConMap.inDomain(TE, tycon) then
		(* [Section 3.5, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
		TyConMap.insert(TE, tycon, VIdMap.empty)
	end


    (* Datatype Descriptions *)

    and checkDatDesc(DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	let
	    val  U1      = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val (U2,VE)  = checkConDesc condesc
	    val(VE',TE') = case datdesc_opt
			     of NONE         => ( VIdMap.empty, TyConMap.empty )
			      | SOME datdesc => checkDatDesc datdesc
	in
	    if TyConMap.inDomain(TE', tycon) then
		(* [Section 3.5, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else if not(TyVarSet.isSubset(U2, U1)) then
		(* [Section 3.5,4th bullet]*)
		error(I, "free type variables in datatype description")
	    else
	    ( VIdMap.unionWithi (fn(vid,_,_) =>
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate data cnstructor ", vid)) (VE,VE')
	    , TyConMap.insert(TE', tycon, VE)
	    )
	end


    (* Constructor Descriptions *)

    and checkConDesc(ConDesc(I, vid, ty_opt, condesc_opt)) =
	let
	    val  U      = case ty_opt
			    of NONE    => TyVarSet.empty
			     | SOME ty => SyntacticRestrictionsCore.checkTy ty
	    val (U',VE) = case condesc_opt
			    of NONE         => ( TyVarSet.empty, VIdMap.empty )
			     | SOME condesc => checkConDesc condesc
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)
	    else if not(SyntacticRestrictionsCore.validConBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specifiation of identifier ", vid)
	    else
		( TyVarSet.union(U, U'), VIdMap.insert(VE, vid, IdStatus.c) )
	end


    (* Exception Description *)

    and checkExDesc(ExDesc(I, vid, ty_opt, exdesc_opt)) =
	let
	    val U  = case ty_opt
		       of NONE    => TyVarSet.empty
			| SOME ty => SyntacticRestrictionsCore.checkTy ty
	    val VE = case exdesc_opt
		       of NONE        => VIdMap.empty
			| SOME exdesc => checkExDesc exdesc
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else if not(SyntacticRestrictionsCore.validConBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specification of identifier ", vid)
	    else
		VIdMap.insert(VE, vid, IdStatus.e)
	end


    (* Structure Descriptions *)

    and checkStrDesc(B, StrDesc(I, strid, sigexp, strdesc_opt)) =
	let
	    val E  = checkSigExp(B, sigexp)
	    val SE = case strdesc_opt
		       of NONE         => StrIdMap.empty
		        | SOME strdesc => checkStrDesc(B, strdesc)
	in
	    if StrIdMap.inDomain(SE, strid) then
		(* [Section 3.5, 2nd bullet] *)
		errorStrId(I, "duplicate structure identifier ", strid)
	    else
		StrIdMap.insert(SE, strid, E)
	end


    (* Functor Declarations *)

    and checkFunDec(B, FunDec(I, funbind)) =
	let
	    val F = checkFunBind(B, funbind)
	in
	    F
	end


    (* Functor Bindings *)

    and checkFunBind(B, FunBind(I, funid, strid, sigexp, strexp, funbind_opt)) =
	let
	    val E1 = checkSigExp(B, sigexp)
	    val E2 = checkStrExp(B plusSE StrIdMap.singleton(strid, E1), strexp)
	    val F  = case funbind_opt
		       of NONE         => FunIdMap.empty
			| SOME funbind => checkFunBind(B, funbind)
	in
	    if FunIdMap.inDomain(F, funid) then
		(* [Section 3.5, 1st bullet] *)
		errorFunId(I, "duplicate functor identifier ", funid)
	    else
		FunIdMap.insert(F, funid, E2)
	end


    (* Top-level Declarations *)

    and checkTopDec(B, STRDECTopDec(I, strdec, topdec_opt)) =
	let
	    val E   = checkStrDec(B, strdec)
	    val B'  = case topdec_opt
			of NONE        => BindingBasis.empty
			 | SOME topdec => checkTopDec(B plusE E, topdec)
	in
	    BindingBasis.fromE E plus B'
	end

      | checkTopDec(B, SIGDECTopDec(I, sigdec, topdec_opt)) =
	let
	    val G   = checkSigDec(B, sigdec)
	    val B'  = case topdec_opt
			of NONE        => BindingBasis.empty
			 | SOME topdec => checkTopDec(B plusG G, topdec)
	in
	    BindingBasis.fromG G plus B'
	end

      | checkTopDec(B, FUNDECTopDec(I, fundec, topdec_opt)) =
	let
	    val F   = checkFunDec(B, fundec)
	    val B'  = case topdec_opt
			of NONE        => BindingBasis.empty
			 | SOME topdec => checkTopDec(B plusF F, topdec)
	in
	    BindingBasis.fromF F plus B'
	end
end;
