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
	    val (E, strdec) = checkStrDec(B, strdec)
	in
	    (E, STRUCTStrExp(I, strdec))
	end

      | checkStrExp(B, IDStrExp(I, longstrid)) =
	let
	    val E = case BindingBasis.findLongStrId(B, longstrid)
		      of SOME E => E
		       | NONE   => BindingEnv.empty (* actually an error *)
	in
	    (E, IDStrExp(I, longstrid))
	end

      | checkStrExp(B, COLONStrExp(I, strexp, sigexp)) =
	let
	    val (E1, strexp) = checkStrExp(B, strexp)
	    val (E2, sigexp) = checkSigExp(B, sigexp)
	in
	    (E2, COLONStrExp(I, strexp, sigexp))
	end

      | checkStrExp(B, SEALStrExp(I, strexp, sigexp)) =
	let
	    val (E1, strexp) = checkStrExp(B, strexp)
	    val (E2, sigexp) = checkSigExp(B, sigexp)
	in
	    (E2, SEALStrExp(I, strexp, sigexp))
	end

      | checkStrExp(B, APPStrExp(I, funid, strexp)) =
	let
	    val (E1, strexp) = checkStrExp(B, strexp)
	    val E2 = case BindingBasis.findFunId(B, funid)
		               of SOME E => E
		                | NONE   => BindingEnv.empty (* actually an error *)
	in
	    (E2, APPStrExp(I, funid, strexp))
	end

      | checkStrExp(B, LETStrExp(I, strdec, strexp)) =
	let
	    val (E1, strdec) = checkStrDec(B, strdec)
	    val (E2, strexp) = checkStrExp(B plusE E1, strexp)
	in
	    (E2, LETStrExp(I, strdec, strexp))
	end


    (* Structure-level Declarations *)

    and checkStrDec(B, DECStrDec(I, dec)) =
	let
	    val (E, dec) = SyntacticRestrictionsCore.checkDec(BindingBasis.Cof B, dec)
	in
	    (E, DECStrDec(I,dec))
	end

      | checkStrDec(B, STRUCTUREStrDec(I, strbind)) =
	let
	    val (SE, strbind) = checkStrBind(B, strbind)
	in
	    (BindingEnv.fromSE SE, STRUCTUREStrDec(I,strbind))
	end

      | checkStrDec(B, LOCALStrDec(I, strdec1, strdec2)) =
	let
	    val (E1, strdec1) = checkStrDec(B, strdec1)
	    val (E2, strdec2) = checkStrDec(B plusE E1, strdec2)
	in
	    (E2, LOCALStrDec(I, strdec1, strdec2))
	end

      | checkStrDec(B, EMPTYStrDec(I)) =
	    (BindingEnv.empty, EMPTYStrDec(I))

      | checkStrDec(B, SEQStrDec(I, strdec1, strdec2)) =
	let
	    val (E1, strdec1) = checkStrDec(B, strdec1)
	    val (E2, strdec2) = checkStrDec(B plusE E1, strdec2)
	in
	    (BindingEnv.plus(E1, E2), SEQStrDec(I, strdec1, strdec2))
	end


    (* Structure Bindings *)

    and checkStrBind(B, StrBind(I, strid, strexp, strbind_opt)) =
	let
	    val (E, strexp)  = checkStrExp(B, strexp)
	    val (SE, strbind_opt) = case strbind_opt
		                     of NONE         => (StrIdMap.empty, NONE)
		                      | SOME strbind => let val (s,p) = checkStrBind(B, strbind)
                                                       in (s, SOME p) end
	in
	    if StrIdMap.inDomain(SE, strid) then
		(* [Section 3.5, 1st bullet] *)
		errorStrId(I, "duplicate structure identifier ", strid)
	    else

		(StrIdMap.insert(SE, strid, E), StrBind(I, strid, strexp, strbind_opt))
	end


    (* Signature Expressions *)

    and checkSigExp(B, SIGSigExp(I, spec)) =
	let
	    val (E, spec) = checkSpec(B, spec)
	in
	    (E, SIGSigExp(I, spec))
	end

      | checkSigExp(B, IDSigExp(I, sigid)) =
	let
	    val E = case BindingBasis.findSigId(B, sigid)
		      of SOME E => E
		       | NONE   => BindingEnv.empty (* actually an error *)
	in
	    (E, IDSigExp(I, sigid))
	end

      | checkSigExp(B, WHERETYPESigExp(I, sigexp, tyvarseq, longtycon, ty)) =
	let
	    val (E, sigexp)  = checkSigExp(B, sigexp)
	    val U1 = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val U2 = SyntacticRestrictionsCore.checkTy ty
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* [Section 3.5, 4th bullet] *)
		error(I, "free type variables in type realisation")
	    else
		(E, WHERETYPESigExp(I, sigexp, tyvarseq, longtycon, ty))
	end


    (* Signature Declarations *)

    and checkSigDec(B, SigDec(I, sigbind)) =
	let
	    val (G, sigbind) = checkSigBind(B, sigbind)
	in
	    (G, SigDec(I, sigbind))
	end


    (* Signature Bindings *)

    and checkSigBind(B, SigBind(I, sigid, sigexp, sigbind_opt)) =
	let
	    val (E, sigexp) = checkSigExp(B, sigexp)
	    val (G, sigbind) = case sigbind_opt
		                of NONE         => (SigIdMap.empty, NONE)
		                 | SOME sigbind => let val (g,p) = checkSigBind(B, sigbind)
                                                  in (g, SOME p) end
	in
	    if SigIdMap.inDomain(G, sigid) then
		(* [Section 3.5, 1st bullet] *)
		errorSigId(I, "duplicate signature identifier ", sigid)
	    else
		(SigIdMap.insert(G, sigid, E), SigBind(I, sigid, sigexp, sigbind))
	end


    (* Specifications *)

    and checkSpec(B, VALSpec(I, valdesc)) =
	let
	    val (VE, valdesc) = checkValDesc valdesc
	in
	    (BindingEnv.fromVE VE, VALSpec(I, valdesc))
	end

      | checkSpec(B, TYPESpec(I, typdesc)) =
	let
	    val (TE, typdesc) = checkTypDesc typdesc
	in
	    (BindingEnv.fromTE TE, TYPESpec(I, typdesc))
	end

      | checkSpec(B, EQTYPESpec(I, typdesc)) =
	let
	    val (TE, typdes) = checkTypDesc typdesc
	in
	    (BindingEnv.fromTE TE, EQTYPESpec(I, typdesc))
	end

      | checkSpec(B, DATATYPESpec(I, datdesc)) =
	let
	    val ((VE,TE), datdesc) = checkDatDesc datdesc
	in
	    (BindingEnv.fromVEandTE(VE,TE), DATATYPESpec(I, datdesc))
	end

      | checkSpec(B, DATATYPE2Spec(I, tycon, longtycon)) =
	let
	    val VE = case BindingBasis.findLongTyCon(B, longtycon)
		       of SOME VE => VE
			| NONE    => VIdMap.empty (* actually an error *)
	    val TE = TyConMap.singleton(tycon, VE)
	in
	    (BindingEnv.fromVEandTE(VE,TE), DATATYPE2Spec(I, tycon, longtycon))
	end

      | checkSpec(B, EXCEPTIONSpec(I, exdesc)) =
	let
	    val (VE, exdesc) = checkExDesc exdesc
	in
	    (BindingEnv.fromVE VE, EXCEPTIONSpec(I, exdesc))
	end

      | checkSpec(B, STRUCTURESpec(I, strdesc)) =
	let
	    val (SE, strdesc) = checkStrDesc(B, strdesc)
	in
	    (BindingEnv.fromSE SE, STRUCTURESpec(I, strdesc))
	end

      | checkSpec(B, INCLUDESpec(I, sigexp)) =
	let
	    val (E, sigexp) = checkSigExp(B, sigexp)
	in
	    (E, INCLUDESpec(I, sigexp))
	end

      | checkSpec(B, EMPTYSpec(I)) =
	    (BindingEnv.empty, EMPTYSpec(I))

      | checkSpec(B, SEQSpec(I, spec1, spec2)) =
	let
	    val (E1, spec1) = checkSpec(B, spec1)
	    val (E2, spec2) = checkSpec(B plusE E1, spec2)
	in
	    (BindingEnv.plus(E1, E2), SEQSpec(I, spec1, spec2))
	end

      | checkSpec(B, SHARINGTYPESpec(I, spec, longtycons)) =
	let
	    val (E, spec) = checkSpec(B, spec)
	in
	    (E, SHARINGTYPESpec(I, spec, longtycons))
	end

      | checkSpec(B, SHARINGSpec(I, spec, longstrids)) =
	(* [Appendix A] *)
	let
	    val (E, spec) = checkSpec(B, spec)
	in
	    (E, SHARINGSpec(I, spec, longstrids))
	end


    (* Value Descriptions *)

    and checkValDesc(ValDesc(I, vid, ty, valdesc_opt)) =
	let
	    val U  = SyntacticRestrictionsCore.checkTy ty
	    val (VE, valdesc) = case valdesc_opt
		                 of NONE         => (VIdMap.empty, NONE)
			          | SOME valdesc => let val (v,p) = checkValDesc valdesc
                                                   in (v, SOME p) end
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate variable ", vid)
	    else if not(SyntacticRestrictionsCore.validBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specification of identifier ", vid)
	    else
		(VIdMap.insert(VE, vid, IdStatus.v), ValDesc(I, vid, ty, valdesc))
	end


    (* Type Descriptions *)

    and checkTypDesc(TypDesc(I, tyvarseq, tycon, typdesc_opt)) =
	let
	    val U  = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val (TE, typdesc) = case typdesc_opt
		                 of NONE         => (TyConMap.empty, NONE)
			          | SOME typdesc => let val (t,p) = checkTypDesc typdesc
                                                   in (t, SOME p) end
	in
	    if TyConMap.inDomain(TE, tycon) then
		(* [Section 3.5, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
		(TyConMap.insert(TE, tycon, VIdMap.empty), TypDesc(I, tyvarseq, tycon, typdesc))
	end


    (* Datatype Descriptions *)

    and checkDatDesc(DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	let
	    val  U1      = SyntacticRestrictionsCore.checkTyVarseq tyvarseq
	    val ((U2,VE), condesc)  = checkConDesc condesc
	    val ((VE',TE'), datdesc) = case datdesc_opt
			     of NONE         => (( VIdMap.empty, TyConMap.empty ), NONE)
			      | SOME datdesc => let val (v,p) = checkDatDesc datdesc
                                               in (v, SOME p) end 
	in
	    if TyConMap.inDomain(TE', tycon) then
		(* [Section 3.5, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else if not(TyVarSet.isSubset(U2, U1)) then
		(* [Section 3.5,4th bullet]*)
		error(I, "free type variables in datatype description")
	    else
	    (( VIdMap.unionWithi (fn(vid,_,_) =>
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate data cnstructor ", vid)) (VE,VE')
	    , TyConMap.insert(TE', tycon, VE)
	    ), DatDesc(I, tyvarseq, tycon, condesc, datdesc))
	end


    (* Constructor Descriptions *)

    and checkConDesc(ConDesc(I, vid, ty_opt, condesc_opt)) =
	let
	    val  U      = case ty_opt
			    of NONE    => TyVarSet.empty
			     | SOME ty => SyntacticRestrictionsCore.checkTy ty
	    val ((U',VE), condesc) = case condesc_opt
			    of NONE         => (( TyVarSet.empty, VIdMap.empty ), NONE)
			     | SOME condesc => let val (u,p) = checkConDesc condesc
                                              in (u, SOME p) end
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)
	    else if not(SyntacticRestrictionsCore.validConBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specifiation of identifier ", vid)
	    else
		(( TyVarSet.union(U, U'), VIdMap.insert(VE, vid, IdStatus.c) ),
                 ConDesc(I, vid, ty_opt, condesc))
	end


    (* Exception Description *)

    and checkExDesc(ExDesc(I, vid, ty_opt, exdesc_opt)) =
	let
	    val U  = case ty_opt
		       of NONE    => TyVarSet.empty
			| SOME ty => SyntacticRestrictionsCore.checkTy ty
	    val (VE,exdesc) = case exdesc_opt
		       of NONE        => (VIdMap.empty, NONE)
			| SOME exdesc => let val (v, p) = checkExDesc exdesc
                                        in (v, SOME p) end
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 3.5, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else if not(SyntacticRestrictionsCore.validConBindVId vid) then
		(* [Section 3.5, 5th bullet] *)
		errorVId(I, "illegal specification of identifier ", vid)
	    else
		(VIdMap.insert(VE, vid, IdStatus.e),
                 ExDesc(I, vid, ty_opt, exdesc))
	end


    (* Structure Descriptions *)

    and checkStrDesc(B, StrDesc(I, strid, sigexp, strdesc_opt)) =
	let
	    val (E,sigexp)  = checkSigExp(B, sigexp)
	    val (SE,strdesc) = case strdesc_opt
		       of NONE         => (StrIdMap.empty, NONE)
		        | SOME strdesc => let val (s,p) = checkStrDesc(B, strdesc)
                                         in (s, SOME p) end
	in
	    if StrIdMap.inDomain(SE, strid) then
		(* [Section 3.5, 2nd bullet] *)
		errorStrId(I, "duplicate structure identifier ", strid)
	    else
		(StrIdMap.insert(SE, strid, E),
                 StrDesc(I, strid, sigexp, strdesc))
	end


    (* Functor Declarations *)

    and checkFunDec(B, FunDec(I, funbind)) =
	let
	    val (F,funbind) = checkFunBind(B, funbind)
	in
	    (F, FunDec(I, funbind))
	end


    (* Functor Bindings *)

    and checkFunBind(B, FunBind(I, funid, strid, sigexp, strexp, funbind_opt)) =
	let
	    val (E1,sigexp) = checkSigExp(B, sigexp)
	    val (E2,strexp) = checkStrExp(B plusSE StrIdMap.singleton(strid, E1), strexp)
	    val (F,funbind)  = case funbind_opt
		       of NONE         => (FunIdMap.empty, NONE)
			| SOME funbind => let val (f,p) = checkFunBind(B, funbind)
                                         in (f,SOME p) end
	in
	    if FunIdMap.inDomain(F, funid) then
		(* [Section 3.5, 1st bullet] *)
		errorFunId(I, "duplicate functor identifier ", funid)
	    else
	       (FunIdMap.insert(F, funid, E2),
                FunBind(I, funid, strid, sigexp, strexp, funbind))
	end


    (* Top-level Declarations *)

    and checkTopDec(B, STRDECTopDec(I, strdec, topdec_opt)) =
	let
	    val (E, strdec)   = checkStrDec(B, strdec)
	    val (B', topdec)  = case topdec_opt
			of NONE        => (BindingBasis.empty, NONE)
			 | SOME topdec => let val (b,p) = checkTopDec(B plusE E, topdec)
                                         in (b, SOME p) end
	in
	    (BindingBasis.fromE E plus B', STRDECTopDec(I, strdec, topdec))
	end

      | checkTopDec(B, SIGDECTopDec(I, sigdec, topdec_opt)) =
	let
	    val (G,sigdec)   = checkSigDec(B, sigdec)
	    val (B',topdec)  = case topdec_opt
			of NONE        => (BindingBasis.empty, NONE)
			 | SOME topdec => let val (b,p) = checkTopDec(B plusG G, topdec)
                                         in (b, SOME p) end
	in
	    (BindingBasis.fromG G plus B', SIGDECTopDec(I, sigdec, topdec))
	end

      | checkTopDec(B, FUNDECTopDec(I, fundec, topdec_opt)) =
	let
	    val (F,fundec)   = checkFunDec(B, fundec)
	    val (B',topdec)  = case topdec_opt
			of NONE        => (BindingBasis.empty, NONE)
			 | SOME topdec => let val (b,p) = checkTopDec(B plusF F, topdec)
                                         in (b, SOME p) end
	in
	    (BindingBasis.fromF F plus B', FUNDECTopDec(I, fundec, topdec))
	end
end;
