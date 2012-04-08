(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML modules elaboration
 *
 * Definition, Sections 5.7 and 3.5
 *
 * Notes:
 *   - To implement the 3rd restriction in 4.11 some elab functions are
 *     passed an additional boolean argument to recognise being on the toplevel.
 *   - Another bug in the Definition -- rules 64 and 78 need additional
 *     side conditions to ensure well-formedness of the constructed realisation:
 *     (64) t in TyName^(k)
 *     (78) t_i in TyName^(k), i = 1..n
 *)

structure ElabModule : ELAB_MODULE =
struct
    (* Import *)

    open GrammarModule
    open StaticObjectsModule
    open StaticObjectsCore
    open Error


    (* Helpers for basis modification *)

    val plus    = StaticBasis.plus
    val plusT   = StaticBasis.plusT
    val oplusSE = StaticBasis.oplusSE
    val oplusG  = StaticBasis.oplusG
    val oplusF  = StaticBasis.oplusF
    val oplusE  = StaticBasis.oplusE

    infix plus plusT oplusG oplusF oplusE oplusSE


    (* Inference rules [Section 5.7] *)


    (* Structure Expressions *)

    fun elabStrExp(B, STRUCTStrExp(I, strdec)) =
	(* [Rule 50] *)
	let
	    val E = elabStrDec false (B, strdec)
	in
	    E
	end

      | elabStrExp(B, IDStrExp(I, longstrid)) =
	(* [Rule 51] *)
	let
	    val E = case StaticBasis.findLongStrId(B, longstrid)
		      of SOME E => E
		       | NONE =>
			 errorLongStrId(I, "unknown structure ", longstrid)
	in
	    E
	end

      | elabStrExp(B, COLONStrExp(I, strexp, sigexp)) =
	(* [Rule 52] *)
	let
	    val E      = elabStrExp(B, strexp)
	    val Sigma  = elabSigExp(B, sigexp)
	    val (E',_) = Sig.match(E, Sigma)
			 handle Sig.Match =>
				error(I, "structure does not match constraint")
	in
	    E'
	end

      | elabStrExp(B, SEALStrExp(I, strexp, sigexp)) =
	(* [Rule 53] *)
	let
	    val E       = elabStrExp(B, strexp)
	    val (T',E') = Sig.rename(elabSigExp(B, sigexp))
	    val (E'',_) = Sig.match(E, (T',E'))
			  handle Sig.Match =>
				 error(I, "structure does not match constraint")
	in
	    if TyNameSet.isEmpty
		    (TyNameSet.intersection(T', StaticBasis.tynames B)) then
		E'
	    else
		(* Side condition is always ensured by renaming. *)
		error(I, "inconsistent type names")
	end

      | elabStrExp(B, APPStrExp(I, funid, strexp)) =
	(* [Rule 54] *)
	let
	    val E = elabStrExp(B, strexp)
	    val (T1,(E1,(T1',E1'))) =
		      case StaticBasis.findFunId(B, funid)
			of SOME Phi => Phi
			 | NONE     => errorFunId(I, "unknown functor ", funid)
	    val (E'',phi) = Sig.match(E, (T1,E1))
			    handle Sig.Match =>
				error(I, "structure does not match constraint")
	    val (T',E')   = Sig.rename (T1', StaticEnv.realise phi E1')
	in
	    if TyNameSet.isEmpty
		(TyNameSet.intersection(TyNameSet.union(StaticEnv.tynames E,
							StaticBasis.tynames B),
					T')) then
		E'
	    else
		(* Side condition is always ensured by renaming. *)
		error(I, "inconsistent type names")
	end

      | elabStrExp(B, LETStrExp(I, strdec, strexp)) =
	(* [Rule 55] *)
	let
	    val E1 = elabStrDec false (B, strdec)
	    val E2 = elabStrExp(B oplusE E1, strexp)
	in
	    E2
	end


    (* Structure-level Declarations *)

    and elabStrDec toplevel (B, DECStrDec(I, dec)) =
	(* [Rule 56] *)
	let
	    val E = ElabCore.elabDec toplevel (StaticBasis.Cof B, dec)
	in
	    E
	end

      | elabStrDec toplevel (B, STRUCTUREStrDec(I, strbind)) =
	(* [Rule 57] *)
	let
	    val SE = elabStrBind(B, strbind)
	in
	    StaticEnv.fromSE SE
	end

      | elabStrDec toplevel (B, LOCALStrDec(I, strdec1, strdec2)) =
	(* [Rule 58] *)
	let
	    val E1 = elabStrDec false (B, strdec1)
	    val E2 = elabStrDec false (B oplusE E1, strdec2)
	in
	    E2
	end

      | elabStrDec toplevel (B, EMPTYStrDec(I)) =
	(* [Rule 59] *)
	StaticEnv.empty

      | elabStrDec toplevel (B, SEQStrDec(I, strdec1, strdec2)) =
	(* [Rule 60] *)
	let
	    val E1 = elabStrDec toplevel (B, strdec1)
	    val E2 = elabStrDec toplevel (B oplusE E1, strdec2)
	in
	    StaticEnv.plus(E1,E2)
	end


    (* Structure Bindings *)

    and elabStrBind(B, StrBind(I, strid, strexp, strbind_opt)) =
	(* [Rule 61] *)
	let
	    val E  = elabStrExp(B, strexp)
	    val SE = case strbind_opt
		       of NONE         => StrIdMap.empty
		        | SOME strbind =>
			  elabStrBind(B plusT StaticEnv.tynames E, strbind)
	in
	    StrIdMap.insert(SE, strid, E)
	end


    (* Signature Expressions *)

    and elabSigExpE(B, SIGSigExp(I, spec)) =
	(* [Rule 62] *)
	let
	    val E = elabSpec(B, spec)
	in
	    E
	end

      | elabSigExpE(B, IDSigExp(I, sigid)) =
	(* [Rule 63] *)
	let
	    val (T,E) = case StaticBasis.findSigId(B, sigid)
			  of SOME Sigma => Sig.rename Sigma
			   | NONE => errorSigId(I, "unknown signature ",sigid)
	in
	    E
	end

      | elabSigExpE(B, WHERETYPESigExp(I, sigexp, tyvarseq, longtycon, ty)) =
	(* [Rule 64] *)
	let
	    val E      = elabSigExpE(B, sigexp)
	    val (U,alphas) = ElabCore.tyvars tyvarseq
	    val tau    = ElabCore.elabTy(StaticBasis.Cof B, ty)
	    val t      = case StaticEnv.findLongTyCon(E,longtycon)
			   of NONE =>
			      errorLongTyCon(I, "unknown type ", longtycon)
			    | SOME(theta,VE) =>
			 case TypeFcn.toTyName theta
			   of NONE =>
			      errorLongTyCon(I, "non-flexible type ", longtycon)
			    | SOME t => t
	    val  _     = if not(TyNameSet.member(StaticBasis.Tof B, t)) then ()
			 else errorLongTyCon(I, "rigid type ", longtycon)
	    val phi    = TyNameMap.singleton(t, (alphas,tau))
	    val  _     = if not(TyName.admitsEquality t)
			 orelse TypeFcn.admitsEquality (alphas,tau) then () else
			  error(I, "type realisation does not respect equality")
	    val  _     = if TyName.arity t = List.length alphas then () else
			  error(I, "type realisation does not respect arity")
	    val E'     = StaticEnv.realise phi E
	    val  _     = if StaticEnv.isWellFormed E' then () else
			  error(I, "type realisation does not respect datatype")
	in
	    E'
	end

    and elabSigExp(B, sigexp) =
	(* [Rule 65] *)
	let
	    val E = elabSigExpE(B, sigexp)
	    val T = TyNameSet.difference(StaticEnv.tynames E, StaticBasis.Tof B)
	in
	    (T,E)
	end


    (* Signature Declarations *)

    and elabSigDec(B, SigDec(I, sigbind)) =
	(* [Rule 66] *)
	let
	    val G = elabSigBind(B, sigbind)
	in
	    G
	end


    (* Signature Bindings *)

    and elabSigBind(B, SigBind(I, sigid, sigexp, sigbind_opt)) =
	(* [Rule 67] *)
	let
	    val Sigma = elabSigExp(B, sigexp)
	    val G     = case sigbind_opt
			  of NONE         => SigIdMap.empty
			   | SOME sigbind => elabSigBind(B, sigbind)
	in
	    SigIdMap.insert(G, sigid, Sigma)
	end


    (* Specifications *)

    and elabSpec(B, VALSpec(I, valdesc)) =
	(* [Rule 68] *)
	let
	    val VE = elabValDesc(StaticBasis.Cof B, valdesc)
	in
	    StaticEnv.fromVE(StaticEnv.Clos VE)
	end

      | elabSpec(B, TYPESpec(I, typdesc)) =
	(* [Rule 69] *)
	let
	    val TE = elabTypDesc false (StaticBasis.Cof B, typdesc)
	in
	    if List.all (fn(t,VE) =>
			 not(TyName.admitsEquality(valOf(TypeFcn.toTyName t))))
			(TyConMap.listItems TE) then
		StaticEnv.fromTE TE
	    else
		(* Side condition is always ensured by elabTypDesc false. *)
		error(I, "inconsistent type names")
	end

      | elabSpec(B, EQTYPESpec(I, typdesc)) =
	(* [Rule 70] *)
	let
	    val TE = elabTypDesc true (StaticBasis.Cof B, typdesc)
	in
	    if List.all (fn(t,VE) =>
			 TyName.admitsEquality(valOf(TypeFcn.toTyName t)))
			(TyConMap.listItems TE) then
		StaticEnv.fromTE TE
	    else
		(* Side condition is always ensured by elabTypDesc true. *)
		error(I, "inconsistent type names")
	end

      | elabSpec(B, DATATYPESpec(I, datdesc)) =
	(* [Rule 71] *)
	let
	    val      TE1  = lhsDatDesc datdesc
	    val (VE2,TE2) = elabDatDesc(Context.oplusTE(StaticBasis.Cof B,TE1),
					datdesc)
	    val (TE, VE)  = StaticEnv.maximiseEquality(TE2,VE2)
	in
	    if List.all (fn(t,VE') =>
			    not(TyNameSet.member(StaticBasis.tynames B,
						 valOf(TypeFcn.toTyName t))))
			(TyConMap.listItems TE) then
		StaticEnv.fromVEandTE(VE,TE)
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end

      | elabSpec(B, DATATYPE2Spec(I, tycon, longtycon)) =
	(* [Rule 72] *)
	let
	    val (theta,VE) = case StaticBasis.findLongTyCon(B, longtycon)
			      of SOME tystr => tystr
			       | NONE =>
				 errorLongTyCon(I, "unknown type ", longtycon)
	    val  TE        = TyConMap.singleton(tycon, (theta,VE))
	in
	    StaticEnv.fromVEandTE(VE,TE)
	end

      | elabSpec(B, EXCEPTIONSpec(I, exdesc)) =
	(* [Rule 73] *)
	let
	    val VE = elabExDesc(StaticBasis.Cof B, exdesc)
	in
	    StaticEnv.fromVE VE
	end

      | elabSpec(B, STRUCTURESpec(I, strdesc)) =
	(* [Rule 74] *)
	let
	    val SE = elabStrDesc(B, strdesc)
	in
	    StaticEnv.fromSE SE
	end

      | elabSpec(B, INCLUDESpec(I, sigexp)) =
	(* [Rule 75] *)
	let
	    val E = elabSigExpE(B, sigexp)
	in
	    E
	end

      | elabSpec(B, EMPTYSpec(I)) =
	(* [Rule 76] *)
	StaticEnv.empty

      | elabSpec(B, SEQSpec(I, spec1, spec2)) =
	(* [Rule 77] *)
	let
	    val E1 = elabSpec(B, spec1)
	    val E2 = elabSpec(B oplusE E1, spec2)
	    val _  = if StaticEnv.disjoint(E1,E2) then () else
		     error(I, "duplicate specifications in signature")
	in
	    StaticEnv.plus(E1,E2)
	end

      | elabSpec(B, SHARINGTYPESpec(I, spec, longtycons)) =
	(* [Rule 78] *)
	let
	    val E  = elabSpec(B, spec)
	    val ts =
		List.map
		(fn longtycon =>
		 case StaticEnv.findLongTyCon(E, longtycon)
		   of NONE =>
			errorLongTyCon(I, "unknown type ", longtycon)
		    | SOME(theta,VE) =>
		 case TypeFcn.toTyName theta
		   of NONE =>
			errorLongTyCon(I, "non-flexible type ", longtycon)
		    | SOME t =>
		      if TyNameSet.member(StaticBasis.Tof B, t) then
			errorLongTyCon(I, "rigid type ", longtycon)
		      else
			t
		)
		longtycons
	    val arity    = TyName.arity(List.hd ts)
	    val equality = List.exists TyName.admitsEquality ts
	    val span  = List.foldl
				(fn(t, span) => Int.max(TyName.span t, span))
				0 ts
            val lv = TyName.level (List.hd ts)
	    val t     = TyName.tyname(TyName.toString(List.hd ts),
				      arity, equality, span, lv)
	    val  _    = if List.all (fn ti => TyName.arity ti = arity) ts
			then () else
			  error(I, "type sharing does not respect arity")
	    val phi   = List.foldl
			    (fn(ti, phi) =>
				TyNameMap.insert(phi, ti, TypeFcn.fromTyName t))
			    TyNameMap.empty ts
	in
	    if TyNameSet.isEmpty
		(TyNameSet.intersection(TyNameSet.fromList ts,
					StaticBasis.tynames B)) then
		StaticEnv.realise phi E
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end

      | elabSpec(B, SHARINGSpec(I, spec, longstrids)) =
	(* [Appendix A] *)
	let
	    fun shareFlexibleTyName(t1, t2, phi) =
		let
		    val t = TyName.tyname(TyName.toString t1, TyName.arity t1,
					  TyName.admitsEquality t1 orelse
					      TyName.admitsEquality t2,
					  Int.max(TyName.span t1,
						  TyName.span t2),
                                          TyName.level t1)
		    val theta = TypeFcn.fromTyName t
		in
		    TyNameMap.insert(TyNameMap.insert(phi,
			t1, theta),
			t2, theta)
		end

	    fun shareTE(TE1, TE2, phi) =
		TyConMap.foldli
		    (fn(tycon, (theta1,VE1), phi) =>
			case TyConMap.find(TE2, tycon)
			  of NONE             => phi
			   | SOME(theta2,VE2) =>
			case (TypeFcn.toTyName(TypeFcn.realise phi theta1),
			      TypeFcn.toTyName(TypeFcn.realise phi theta2))
			  of (SOME t1, SOME t2) =>
			     if TyNameSet.member(StaticBasis.Tof B, t1)
			     orelse TyNameSet.member(StaticBasis.Tof B,t2) then
				errorTyCon(I, "structure contains rigid type ",
					      tycon)
			     else
				shareFlexibleTyName(t1, t2, phi)
			   | _ =>
			     errorTyCon(I, "structure contains non-flexible \
					   \type ", tycon)
		    )
		    phi TE1

	    fun shareSE(SE1, SE2, phi) =
		StrIdMap.foldli
		    (fn(strid, E1, phi) =>
			case StrIdMap.find(SE2, strid)
			  of NONE    => phi
			   | SOME E2 => shareE(E1, E2, phi)
		    )
		    phi SE1

	    and shareE(Env(SE1,TE1,VE1), Env(SE2,TE2,VE2), phi) =
		let
		    val phi'  = shareTE(TE1, TE2, phi)
		    val phi'' = shareSE(SE1, SE2, phi')
		in
		    phi''
		end

	    fun share1(E1,   [],   phi) = phi
	      | share1(E1, E2::Es, phi) =
		let
		    val phi' = shareE(E1, E2, phi)
		in
		    share1(E1, Es, phi')
		end

	    fun shareAll( [],   phi) = phi
	      | shareAll(E::Es, phi) =
		let
		    val phi' = share1(E, Es, phi)
		in
		    shareAll(Es, phi')
		end

	    val E   = elabSpec(B, spec)
	    val Es  = List.map
			(fn longstrid =>
			 case StaticEnv.findLongStrId(E, longstrid)
			   of SOME E' => E'
			    | NONE =>
			      errorLongStrId(I, "unknown structure ", longstrid)
			) longstrids
	    val phi = shareAll(Es, TyNameMap.empty)
	in
	    if TyNameSet.isEmpty
		   (TyNameSet.intersection
			(TyNameSet.addList(TyNameSet.empty,
					   TyNameMap.listKeys phi),
			 StaticBasis.tynames B)) then
		StaticEnv.realise phi E
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end


    (* Value Descriptions *)

    and elabValDesc(C, ValDesc(I, vid, ty, valdesc_opt)) =
	(* [Rule 79] *)
	let
	    val tau = ElabCore.elabTy(C, ty)
	    val VE  = case valdesc_opt
			of NONE         => VIdMap.empty
			 | SOME valdesc => elabValDesc(C, valdesc)
	in
	    VIdMap.insert(VE, vid, (([],tau),IdStatus.v))
	end


    (* Type Descriptions *)

    and elabTypDesc eq (C, TypDesc(I, tyvarseq, tycon, typdesc_opt)) =
	(* [Rule 80] *)
	let
	    val alphas = #2(ElabCore.tyvars tyvarseq)
	    val k      = List.length alphas
	    val t      = TyName.tyname(TyCon.toString tycon, k, eq, 0, Level.Unknown)
	    val TE     = case typdesc_opt
			   of NONE         => TyConMap.empty
			    | SOME typdesc => 
				let
				    val TE = elabTypDesc eq (C, typdesc)
				in
				    if TyNameSet.member(StaticEnv.tynamesTE TE,
							t) then
					(* Side condition is always ensured
					 * by stamping. *)
					error(I, "inconsistent type names")
				    else
					TE
				end
	    val tau    = Type.fromConsType (List.map Type.fromTyVar alphas, t)
	in
	    TyConMap.insert(TE, tycon, ((alphas,tau), VIdMap.empty))
	end


    (* Datatype Descriptions *)

    and elabDatDesc(C, DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	(* [Rule 81, part 2] *)
	let
	    val (U,alphas)   = ElabCore.tyvars tyvarseq
	    val (alphas,tau) = case Context.findTyCon(C, tycon)
				 of SOME(theta,VE) => theta
				  | NONE => (* lhsDatDesc inserted it! *)
				    raise Fail "ElabCore.elabDatDesc: \
						\tycon not pre-bound"
	    val VE       = elabConDesc(C,tau, condesc)
	    val(VE',TE') = case datdesc_opt
			     of NONE         => ( VIdMap.empty, TyConMap.empty )
			      | SOME datdesc =>
				let
				    val  t = valOf(TypeFcn.toTyName(alphas,tau))
				    val (VE',TE') = elabDatDesc(C, datdesc)
				in
				    if List.all (fn(t',VE'') =>
						t <> valOf(TypeFcn.toTyName t'))
					 	(TyConMap.listItems TE') then
					(VE',TE')
				    else
					(* Side condition is always ensured
					 * by stamping. *)
					error(I, "inconsistent type names")
				end
	    val ClosVE   = StaticEnv.Clos VE
	in
	    ( VIdMap.unionWith #2 (ClosVE,VE')
	    , TyConMap.insert(TE', tycon, ((alphas,tau),ClosVE))
	    )
	end


    (* Constructor Descriptions *)

    and elabConDesc(C,tau, ConDesc(I, vid, ty_opt, condesc_opt)) =
	(* [Rule 82] *)
	let
	    val tau1 = case ty_opt
			 of NONE    => tau
			  | SOME ty =>
			    let
				val tau' = ElabCore.elabTy(C, ty)
			    in
			        Type.fromFunType(tau',tau,ref Level.Unknown,ref Level.Stable)
			    end
	    val VE   = case condesc_opt
			 of NONE         => VIdMap.empty
			  | SOME condesc => elabConDesc(C,tau, condesc)
	in
	    VIdMap.insert(VE, vid, (([],tau1),IdStatus.c))
	end


    (* Exception Description *)

    and elabExDesc(C, ExDesc(I, vid, ty_opt, exdesc_opt)) =
	(* [Rule 83] *)
	let
	    val tau1 = case ty_opt
			 of NONE    => InitialStaticEnv.tauExn
			  | SOME ty =>
			    let
				val tau = ElabCore.elabTy(C, ty)
				val  _  = if TyVarSet.isEmpty(Type.tyvars tau)
					  then () else
					  error(I, "free type variables \
						   \in exception description")
			    in
			        Type.fromFunType(tau, InitialStaticEnv.tauExn,ref Level.Stable,ref Level.Stable)
			    end
	    val VE   = case exdesc_opt
			 of NONE        => VIdMap.empty
			  | SOME exdesc => elabExDesc(C, exdesc)
	in
	    VIdMap.insert(VE, vid, (([],tau1),IdStatus.e))
	end


    (* Structure Descriptions *)

    and elabStrDesc(B, StrDesc(I, strid, sigexp, strdesc_opt)) =
	(* [Rule 84] *)
	let
	    val E  = elabSigExpE(B, sigexp)
	    val SE = case strdesc_opt
		       of NONE         => StrIdMap.empty
		        | SOME strdesc =>
			  elabStrDesc(B plusT StaticEnv.tynames E, strdesc)
	in
	    StrIdMap.insert(SE, strid, E)
	end


    (* Functor Declarations *)

    and elabFunDec(B, FunDec(I, funbind)) =
	(* [Rule 85] *)
	let
	    val F = elabFunBind(B, funbind)
	in
	    F
	end


    (* Functor Bindings *)

    and elabFunBind(B, FunBind(I, funid, strid, sigexp, strexp, funbind_opt)) =
	(* [Rule 86] *)
	let
	    val (T,E) = elabSigExp(B, sigexp)
	    val  E'   = elabStrExp(
			   B oplusSE StrIdMap.singleton(strid, E),
			   strexp)
	    val T'    = TyNameSet.difference(StaticEnv.tynames E',
				TyNameSet.union(StaticBasis.Tof B, T))
	    val F     = case funbind_opt
			  of NONE         => FunIdMap.empty
			   | SOME funbind => elabFunBind(B, funbind)
	in
	    if not(TyNameSet.isEmpty
			(TyNameSet.intersection(T, StaticBasis.tynames B))) then
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	    else
		FunIdMap.insert(F, funid, (T,(E,(T',E'))))
	end


    (* Top-level Declarations *)

    and elabTopDec(B, STRDECTopDec(I, strdec, topdec_opt)) =
	(* [Rule 87] *)
	let
	    val E   = elabStrDec true (B, strdec)
	    val B'  = case topdec_opt
			of NONE        => StaticBasis.empty
			 | SOME topdec => elabTopDec(B oplusE E, topdec)
	    val B'' = StaticBasis.plus
			(StaticBasis.fromTandE(StaticEnv.tynames E, E), B')
	in
	    if not(TyVarSet.isEmpty(StaticBasis.tyvars B'')) then
		error(I, "free type variables on top-level")
	    else if not(StampMap.isEmpty(StaticBasis.undetermined B'')) then
		error(I, "undetermined types on top-level")
	    else
		B''
	end

      | elabTopDec(B, SIGDECTopDec(I, sigdec, topdec_opt)) =
	(* [Rule 88] *)
	let
	    val G   = elabSigDec(B, sigdec)
	    val B'  = case topdec_opt
			of NONE        => StaticBasis.empty
			 | SOME topdec => elabTopDec(B oplusG G, topdec)
	    val B'' = StaticBasis.plus
			(StaticBasis.fromTandG(StaticBasis.tynamesG G, G), B')
	in
	    B''
	end

      | elabTopDec(B, FUNDECTopDec(I, fundec, topdec_opt)) =
	(* [Rule 89] *)
	let
	    val F   = elabFunDec(B, fundec)
	    val B'  = case topdec_opt
			of NONE        => StaticBasis.empty
			 | SOME topdec => elabTopDec(B oplusF F, topdec)
	    val B'' = StaticBasis.plus
			(StaticBasis.fromTandF(StaticBasis.tynamesF F, F), B')
	in
	    if not(TyVarSet.isEmpty(StaticBasis.tyvars B'')) then
		error(I, "free type variables on top-level")
	    else if not(StampMap.isEmpty(StaticBasis.undetermined B'')) then
		error(I, "undetermined types on top-level")
	    else
		B''
	end



    (* Build tentative TE from LHSs of datdesc *)

    and lhsDatDesc(DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	(* [Rule 81, part 1] *)
	let
	    val (U,alphas) = ElabCore.tyvars tyvarseq
	    val k          = List.length alphas
	    val span       = lhsConDesc condesc
	    val t          = TyName.tyname(TyCon.toString tycon, k, true, span, Level.Unknown)
	    val tau        = Type.fromConsType(List.map Type.fromTyVar alphas,t)
	    val TE'        = case datdesc_opt
			       of NONE         => TyConMap.empty
				| SOME datdesc => lhsDatDesc datdesc
	in
	    TyConMap.insert(TE', tycon, ((alphas,tau), VIdMap.empty))
	end

    and lhsConDesc(ConDesc(I, vid, ty_opt, condesc_opt)) =
	case condesc_opt
	  of NONE         => 1
	   | SOME condesc => 1 + lhsConDesc condesc
end;
