(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core elaboration
 *
 * Definition, Sections 4.10, 4.11, 4.6, 4.7, 2.9
 *
 * Notes:
 *   - Elaboration also checks the further restrictions [Section 4.11].
 *   - To implement overloading resolution and checks for flexible records,
 *     we accumulate lists of unresolved types at each value declaration.
 *     This requires an additional argument to most elab functions.
 *   - To implement the 3rd restriction in 4.11 some elab functions are
 *     passed an additional boolean argument to recognise being on the toplevel.
 *   - The definition says that overloaded types get defaulted if the
 *     "surrounding text" does not resolve it. It leaves some freedom to
 *     how large this context may be. We choose the innermost value binding.
 *   - The definition states that "the program context" must determine the
 *     exact type of flexible records, but it does not say how large this
 *     context may be either. Again we choose the innermost surrounding value
 *     declaration.
 *)

structure ElabCore : ELAB_CORE =
struct
    (* Import *)

    open GrammarCore
    open StaticObjectsCore
    open Error

    (* Global type map *)
    structure TMap = FinMapFn(type ord_key = string
                              val compare = String.compare)
    val T : StaticObjectsCore.Type TMap.map ref = ref TMap.empty
    fun getType str = TMap.find(!T, str)
    fun setType (str, ty) =
      T := TMap.insert(!T, str, ty)

    (* Helpers for context modification *)

    val plus         = StaticEnv.plus
    val plusU        = Context.plusU
    val plusVE       = Context.plusVE
    val oplusE       = Context.oplusE
    val oplusTE      = Context.oplusTE
    val oplusVEandTE = Context.oplusVEandTE

    infix plusU plusVE oplusE oplusTE oplusVEandTE



    (* Treating tyvarseqs *)

    fun tyvars(TyVarseq(I, tyvars)) =
	let
	    fun collect(     [],       U) = U
	      | collect(tyvar::tyvars, U) =
		    collect(tyvars, TyVarSet.add(U, tyvar))
	in
	    ( collect(tyvars, TyVarSet.empty), tyvars )
	end


    (* Management of unresolved types [Sections 4.11 and Appendix E] *)

    type unresolved = Info * Type * SCon option

    fun instance (I,utaus) sigma =
	let
	    val (taus,tau) = TypeScheme.instance sigma
	in
	    utaus := List.map (fn tau => (I, tau, NONE))
			      (List.filter Type.isOverloaded taus) @ !utaus;
	    tau
	end

    fun resolve(I, tau, sc_opt) =
	( Type.resolve tau handle Type.Flexible =>
	      (* Further restriction [Section 4.11, item 1] *)
	      error(I, "unresolved flexible record type")
	; case sc_opt
	    of NONE    => ()
	     | SOME sc =>
	       let
	           val t = Type.tyname tau
	       in
		   case sc
		     of SCon.INT(b, s, r) =>
			( Library.intFromString(b, s, SOME t) ; r := SOME t )
		      | SCon.WORD(b, s, r) =>
			( Library.wordFromString(b, s, SOME t) ; r := SOME t )
		      | SCon.CHAR(s, r) =>
			( Library.charFromString(s, SOME t) ; r := SOME t )
		      | SCon.STRING(s, r) =>
			( Library.stringFromString(s, SOME t) ; r := SOME t )
		      | SCon.REAL(s, r) =>
			( Library.realFromString(s, SOME t) ; r := SOME t )
	       end
	       handle Overflow =>
		     (* [Section E.1] *)
		     error(I, "special constant out of range")
	)



    (* Typing special constants [Section 4.1, Appendix E.1] *)

    fun typeSCon (utaus, I) scon =
	let
	    val tau = typeSCon' scon
	in
	    utaus := (I, tau, SOME scon) :: !utaus;
	    tau
	end

    and typeSCon'(SCon.INT _)    = Type.fromOverloadingClass Library.Int
      | typeSCon'(SCon.WORD _)   = Type.fromOverloadingClass Library.Word
      | typeSCon'(SCon.CHAR _)   = Type.fromOverloadingClass Library.Char
      | typeSCon'(SCon.STRING _) = Type.fromOverloadingClass Library.String
      | typeSCon'(SCon.REAL _)   = Type.fromOverloadingClass Library.Real



    (* Inference rules [Section 4.10] *)


    (* Atomic Expressions *)

    fun elabAtExp (utaus, fnmatches) (C, SCONAtExp(I, scon)) =
	(* [Rule 1] *)
	typeSCon (utaus, I) scon

      | elabAtExp (utaus, fnmatches) (C, IDAtExp(I, _, longvid)) =
	(* [Rule 2] *)
	let
	    val (sigma,is) = case Context.findLongVId(C, longvid)
			       of SOME valstr => valstr
			        | NONE =>
				  errorLongVId(I, "unknown identifier ",longvid)
	    val tau = instance (I,utaus) sigma
            val _ = setType (LongVId.toString longvid, tau)
	in
	    tau
	end

      | elabAtExp (utaus, fnmatches) (C, RECORDAtExp(I, exprow_opt)) =
	(* [Rule 3] *)
	let
	    val rho = case exprow_opt
			of NONE        => Type.emptyRow
			 | SOME exprow => elabExpRow (utaus, fnmatches)
						     (C, exprow)
	in
	    Type.fromRowType rho
	end

      | elabAtExp (utaus, fnmatches) (C, LETAtExp(I, dec, exp)) =
	(* [Rule 4] *)
	let
	    val E   = elabDec false (C, dec)
	    val tau = elabExp (utaus, fnmatches) (C oplusE E, exp)
	in
	    if TyNameSet.isSubset(Type.tynames tau, Context.Tof C) then
		tau
	    else
		error(I, "escaping local type name in let expression")
	end

      | elabAtExp (utaus, fnmatches) (C, PARAtExp(I, exp)) =
	(* [Rule 5] *)
	let
	    val tau = elabExp (utaus, fnmatches) (C, exp)
	in
	    tau
	end


    (* Expression Rows *)

    and elabExpRow (utaus, fnmatches) (C, ExpRow(I, lab, exp, exprow_opt)) =
	(* [Rule 6] *)
	let
	    val tau = elabExp (utaus, fnmatches) (C, exp)
	    val rho = case exprow_opt
			of NONE        => Type.emptyRow
			 | SOME exprow => elabExpRow (utaus, fnmatches)
						     (C, exprow)
	in
	    Type.insertRow(rho, lab, tau)
	end


    (* Expressions *)

    and elabExp (utaus, fnmatches) (C, ATExp(I, atexp)) =
	(* [Rule 7] *)
	let
	    val tau = elabAtExp (utaus, fnmatches) (C, atexp)
	in
	    tau
	end

      | elabExp (utaus, fnmatches) (C, APPExp(I, exp, atexp)) =
	(* [Rule 8] *)
	let
	    val tau1 = elabExp (utaus, fnmatches) (C, exp)
	    val tau' = elabAtExp (utaus, fnmatches) (C, atexp)
	    val tau  = Type.guess false
            val tau2 = Type.fromFunType(tau',tau,ref Level.Unknown, ref Level.Unknown)
	in
	    Type.unify(tau1, tau2)
	    handle Type.Unify => error(I, "type mismatch on application");
	    tau
	end

      | elabExp (utaus, fnmatches) (C, COLONExp(I, exp, ty)) =
	(* [Rule 9] *)
	let
	    val tau1 = elabExp (utaus, fnmatches) (C, exp)
	    val tau  = elabTy(C, ty)
	in
	    Type.unify(tau1,tau)
	    handle Type.Unify =>
		   error(I, "expression does not match annotation");
	    tau
	end

      | elabExp (utaus, fnmatches) (C, HANDLEExp(I, exp, match)) =
	(* [Rule 10] *)
	let
	    val tau1 = elabExp (utaus, fnmatches) (C, exp)
	    val tau2 = elabMatch (utaus, fnmatches) (C, match)
	in
	    Type.unify(Type.fromFunType(InitialStaticEnv.tauExn, tau1, ref Level.Stable, ref Level.Stable), tau2)
	    handle Type.Unify =>
		   error(I, "type mismatch in handler");
	    tau1
	end

      | elabExp (utaus, fnmatches) (C, RAISEExp(I, exp)) =
	(* [Rule 11] *)
	let
	    val tau1 = elabExp (utaus, fnmatches) (C, exp)
	in
	    Type.unify(tau1, InitialStaticEnv.tauExn)
	    handle Type.Unify =>
		   error(I, "raised expression is not an exception");
	    Type.guess false
	end

      | elabExp (utaus, fnmatches) (C, FNExp(I, match)) =
	(* [Rule 12] *)
	let
	    val tau = elabMatch (utaus, fnmatches) (C, match)
	in
	    (* Further restriction [Section 4.11, item 2] *)
	    fnmatches := (Context.Eof C, match) :: !fnmatches;
	    tau
	end


    (* Matches *)

    and elabMatch (utaus, fnmatches) (C, Match(I, mrule, match_opt)) =
	(* [Rule 13] *)
	let
	    val tau = elabMrule (utaus, fnmatches) (C, mrule)
	in
	    case match_opt
	      of NONE       => tau
	       | SOME match =>
		 let
		     val tau2 = elabMatch (utaus, fnmatches) (C, match)
		 in
		     Type.unify(tau, tau2)
		     handle Type.Unify =>
			    error(I, "type mismatch between different matches");
		     tau
		 end
	end


    (* Match rules *)

    and elabMrule (utaus, fnmatches) (C, Mrule(I, pat, exp)) =
	(* [Rule 14] *)
	let
	    val (VE,tau) = elabPat utaus (C, pat)
	    val  tau'    = elabExp (utaus, fnmatches) (C plusVE VE, exp)
	in
	    if TyNameSet.isSubset(StaticEnv.tynamesVE VE, Context.Tof C) then
		Type.fromFunType(tau,tau',ref Level.Unknown,ref Level.Unknown)
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end


    (* Declarations *)

    and elabDec toplevel (C, VALDec(I, tyvarseq, valbind)) =
	(* [Rule 15] *)
	let
	    val U' = #1(tyvars(tyvarseq))
		     (* Collect implicitly bound tyvars [Section 4.6] *)
	    val U  = TyVarSet.union(U',
			TyVarSet.difference(ScopeTyVars.unguardedTyVars valbind,
					    Context.Uof C))
	    val utaus     = ref []
	    val fnmatches = ref []
	    val VE        = elabValBind (toplevel, utaus, fnmatches)
					(C plusU U, valbind)
	    val _         = List.app resolve (!utaus)
	    val VE'       = Clos.Clos (C,valbind) VE
	in
	    (* Further restriction [Section 4.11, item 2] *)
	    List.app CheckPattern.checkMatch (!fnmatches);
	    if TyVarSet.isEmpty(
			TyVarSet.intersection(U, StaticEnv.tyvarsVE VE')) then
		StaticEnv.fromVE VE'
	    else
		error(I, "some explicit type variables cannot be generalised")
	end

      | elabDec toplevel (C, TYPEDec(I, typbind)) =
	(* [Rule 16] *)
	let
	    val TE = elabTypBind(C, typbind)
	in
	    StaticEnv.fromTE TE
	end

      | elabDec toplevel (C, DATATYPEDec(I, datbind)) =
	(* [Rule 17] *)
	let
	    val      TE1  = lhsDatBind datbind
	    val (VE2,TE2) = elabDatBind(C oplusTE TE1, datbind)
	    val (TE, VE)  = StaticEnv.maximiseEquality(TE2,VE2)
	in
	    if List.all (fn(t,VE') =>
	 		    not(TyNameSet.member(Context.Tof C,
						 valOf(TypeFcn.toTyName t))))
			(TyConMap.listItems TE) then
		StaticEnv.fromVEandTE(VE,TE)
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end

      | elabDec toplevel (C, DATATYPE2Dec(I, tycon, longtycon)) =
	(* [Rule 18] *)
	let
	    val (theta,VE) = case Context.findLongTyCon(C, longtycon)
			      of SOME tystr => tystr
			       | NONE =>
				 errorLongTyCon(I, "unknown type ", longtycon)
	    val  TE        = TyConMap.singleton(tycon, (theta,VE))
	in
	    StaticEnv.fromVEandTE(VE,TE)
	end

      | elabDec toplevel (C, ABSTYPEDec(I, datbind, dec)) =
	(* [Rule 19] *)
	let
	    val      TE1  = lhsDatBind datbind
	    val (VE2,TE2) = elabDatBind(C oplusTE TE1, datbind)
	    val (TE, VE)  = StaticEnv.maximiseEquality(TE2,VE2)
	    val    E      = elabDec false (C oplusVEandTE (VE,TE), dec)
	in
	    if List.all (fn(t,VE') =>
			    not(TyNameSet.member(Context.Tof C,
						 valOf(TypeFcn.toTyName t))))
			(TyConMap.listItems TE) then
		StaticEnv.Abs(TE,E)
	    else
		(* Side condition is always ensured by stamping. *)
		error(I, "inconsistent type names")
	end

      | elabDec toplevel (C, EXCEPTIONDec(I, exbind)) =
	(* [Rule 20] *)
	let
	    val VE = elabExBind(C, exbind)
	in
	    StaticEnv.fromVE VE
	end

      | elabDec toplevel (C, LOCALDec(I, dec1, dec2)) =
	(* [Rule 21] *)
	let
	    val E1 = elabDec false (C, dec1)
	    val E2 = elabDec false (C oplusE E1, dec2)
	in
	    E2
	end

      | elabDec toplevel (C, OPENDec(I, longstrids)) =
	(* [Rule 22] *)
	let
	    val Es =
		List.map
		    (fn longstrid =>
			case Context.findLongStrId(C, longstrid)
			  of SOME E => E
			   | NONE =>
			     errorLongStrId(I, "unknown structure ", longstrid))
		    longstrids
	in
	    List.foldr StaticEnv.plus StaticEnv.empty Es
	end

      | elabDec toplevel (C, EMPTYDec(I)) =
	(* [Rule 23] *)
	StaticEnv.empty

      | elabDec toplevel (C, SEQDec(I, dec1, dec2)) =
	(* [Rule 24] *)
	let
	    val E1 = elabDec toplevel (C, dec1)
	    val E2 = elabDec toplevel (C oplusE E1, dec2)
	in
	    StaticEnv.plus(E1, E2)
	end


    (* Value Bindings *)

    and elabValBind (toplevel, utaus, fnmatches)
		    (C, PLAINValBind(I, pat, exp, valbind_opt)) =
	(* [Rule 25] *)
	let
	    val (VE,tau1) = elabPat utaus (C, pat)
	    val     tau2  = elabExp (utaus, fnmatches) (C, exp)
	    val  VE'      = case valbind_opt
			      of NONE         => VIdMap.empty
			       | SOME valbind =>
				 elabValBind (toplevel, utaus, fnmatches)
					     (C, valbind)
	in
	    Type.unify(tau1,tau2)
	    handle Type.Unify =>
		   error(I, "type mismatch between pattern and expression");
	    if toplevel then () else
		(* Further restriction [Section 4.11, item 3] *)
		CheckPattern.checkPat(Context.Eof C, pat);
	    VIdMap.unionWith #2 (VE,VE')
	end

      | elabValBind (toplevel, utaus, fnmatches) (C, RECValBind(I, valbind)) =
	(* [Rule 26] *)
	let
	    val VE1 = lhsRecValBind valbind
	    val VE  = elabValBind (toplevel, utaus, fnmatches)
				  (C plusVE VE1, valbind)
	in
	    if not(StaticEnv.equalsVE(VE1, VE)) then
		error(I, "type mismatch in recursive binding")
	    else if TyNameSet.isSubset(StaticEnv.tynamesVE VE,
				       Context.Tof C) then
		VE
	    else
		(* Side condition is always ensured by construction. *)
		error(I, "invalid introduction of type names")
	end


    (* Type Bindings *)

    and elabTypBind(C, TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
	(* [Rule 27] *)
	let
	    val (U,alphas) = tyvars tyvarseq
	    val tau        = elabTy(C, ty)
	    val TE         = case typbind_opt
			       of NONE         => TyConMap.empty
				| SOME typbind => elabTypBind(C, typbind)
	in
	    TyConMap.insert(TE, tycon, ((alphas,tau),VIdMap.empty))
	end


    (* Datatype Bindings *)

    and elabDatBind(C, DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	(* [Rule 28, part 2] *)
	let
	    val (U,alphas)   = tyvars tyvarseq
	    val (alphas,tau) = case Context.findTyCon(C, tycon)
				 of SOME(theta,VE) => theta
				  | NONE => (* lhsDatBind inserted it! *)
				    raise Fail "ElabCore.elabDatBind: \
						\tycon not pre-bound"
	    val VE       = elabConBind(C,tau, conbind)
	    val(VE',TE') = case datbind_opt
			     of NONE         => ( VIdMap.empty, TyConMap.empty )
			      | SOME datbind =>
				let
				    val  t = valOf(TypeFcn.toTyName(alphas,tau))
				    val (VE',TE') = elabDatBind(C, datbind)
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


    (* Constructor Bindings *)

    and elabConBind(C,tau, ConBind(I, _, vid, ty_opt, conbind_opt)) =
	(* [Rule 29] *)
	let
	    val tau1 = case ty_opt
			 of NONE    => tau
			  | SOME ty =>
			    let
				val tau' = elabTy(C, ty)
			    in
			        Type.fromFunType(tau',tau,ref Level.Unknown,ref Level.Stable)
			    end
	    val VE   = case conbind_opt
			 of NONE         => VIdMap.empty
			  | SOME conbind => elabConBind(C,tau, conbind)
	in
	    VIdMap.insert(VE, vid, (([],tau1),IdStatus.c))
	end


    (* Exception Bindings *)

    and elabExBind(C, NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
	(* [Rule 30] *)
	let
	    val tau1 = case ty_opt
			 of NONE    => InitialStaticEnv.tauExn
			  | SOME ty =>
			    let
				val tau = elabTy(C, ty)
			    in
			        Type.fromFunType(tau, InitialStaticEnv.tauExn,ref Level.Stable,ref Level.Stable)
			    end
	    val VE   = case exbind_opt
			 of NONE        => VIdMap.empty
			  | SOME exbind => elabExBind(C, exbind)
	in
	    VIdMap.insert(VE, vid, (([],tau1),IdStatus.e))
	end

      | elabExBind(C, EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
	(* [Rule 31] *)
	let
	    val tau = case Context.findLongVId(C, longvid)
		        of SOME(([],tau),IdStatus.e) => tau
			 | SOME _ =>
			   errorLongVId(I, "non-exception identifier ", longvid)
			 | NONE =>
			   errorLongVId(I, "unknown identifier ", longvid)
	    val VE  = case exbind_opt
			of NONE        => VIdMap.empty
			 | SOME exbind => elabExBind(C, exbind)
	in
	    VIdMap.insert(VE, vid, (([],tau),IdStatus.e))
	end


    (* Atomic Patterns *)

    and elabAtPat utaus (C, WILDCARDAtPat(I)) =
	(* [Rule 32] *)
	( VIdMap.empty, Type.guess false )

      | elabAtPat utaus (C, SCONAtPat(I, scon)) =
	(* [Rule 33] *)
	( VIdMap.empty, typeSCon (utaus,I) scon )

      | elabAtPat utaus (C, IDAtPat(I, _, longvid)) =
	(* [Rule 34 and 35] *)
	let
	    val (strids,vid) = LongVId.explode longvid
	in
	    if List.null strids andalso
	       ( case Context.findVId(C, vid)
		   of NONE           => true
		    | SOME(sigma,is) => is = IdStatus.v )
	    then
		(* [Rule 34] *)
		let
		    val tau = Type.guess false
                    val _ = setType (LongVId.toString longvid, tau)
		in
		    ( VIdMap.singleton(vid, (([],tau),IdStatus.v))
		    , tau )
		end
	    else
		(* [Rule 35] *)
		let
		    val (sigma,is) = case Context.findLongVId(C, longvid)
				       of SOME valstr => valstr
				        | NONE =>
					  errorLongVId(I,"unknown constructor ",
							 longvid)
		    val  tau       = instance (I,utaus) sigma
                    val _ = setType (LongVId.toString longvid, tau)
		in
		    if is = IdStatus.v then
			error(I, "non-constructor long identifier in pattern")
		    else case !tau
		      of ConsType _ => 
			 ( VIdMap.empty, tau )
		       | _ => 
			 error(I, "missing constructor argument in pattern")
		end
	end

      | elabAtPat utaus (C, RECORDAtPat(I, patrow_opt)) =
	(* [Rule 36] *)
	let
	    val (VE,rho) = case patrow_opt
			     of NONE        => (VIdMap.empty, Type.emptyRow)
			      | SOME patrow => elabPatRow utaus (C, patrow)
	    val tau = Type.fromRowType rho
	in
	    utaus := (I, tau, NONE) :: !utaus;
	    (VE, tau)
	end

      | elabAtPat utaus (C, PARAtPat(I, pat)) =
	(* [Rule 37] *)
	let
	    val (VE,tau) = elabPat utaus (C, pat)
	in
	    (VE,tau)
	end


    (* Pattern Rows *)

    and elabPatRow utaus (C, DOTSPatRow(I)) =
	(* [Rule 38] *)
	( VIdMap.empty, Type.guessRow() )

      | elabPatRow utaus (C, FIELDPatRow(I, lab, pat, patrow_opt)) =
	(* [Rule 39] *)
	let
	    val (VE,tau)  = elabPat utaus (C, pat)
	    val (VE',rho) = case patrow_opt
			      of NONE        => (VIdMap.empty, Type.emptyRow)
			       | SOME patrow => elabPatRow utaus (C, patrow)
	in
	    ( VIdMap.unionWithi (fn(vid,_,_) =>
		    errorVId(I, "duplicate variable ", vid)) (VE,VE')
	    , Type.insertRow(rho, lab, tau)
	    )
	end


    (* Patterns *)

    and elabPat utaus (C, ATPat(I, atpat)) =
	(* [Rule 40] *)
	let
	    val (VE,tau) = elabAtPat utaus (C, atpat)
	in
	    (VE,tau)
	end

      | elabPat utaus (C, CONPat(I, _, longvid, atpat)) =
	(* [Rule 41] *)
	let
	    val (sigma,is) = case Context.findLongVId(C, longvid)
			       of SOME valstr => valstr
			        | NONE =>
				errorLongVId(I, "unknown constructor ", longvid)
	    val _          = if is <> IdStatus.v then () else
				errorLongVId(I, "non-constructor ", longvid)
	    val (tau',tau) = case !(instance (I,utaus) sigma)
			       of FunType(tau',tau,mode,lv) => (tau', tau)
			        | _ =>
				errorLongVId(I,"misplaced nullary constructor ",
						longvid)
	    val (VE,tau'2)  = elabAtPat utaus (C, atpat)
	in
	    Type.unify(tau',tau'2)
	    handle Type.Unify =>
		   error(I, "type mismatch in constructor pattern");
	    (VE,tau)
	end

      | elabPat utaus (C, COLONPat(I, pat, ty)) =
	(* [Rule 42] *)
	let
	    val (VE,tau1) = elabPat utaus (C, pat)
	    val     tau   = elabTy(C, ty)
	in
	    Type.unify(tau1,tau)
	    handle Type.Unify => error(I, "pattern does not match annotation");
	    (VE,tau)
	end

      | elabPat utaus (C, ASPat(I, _, vid, ty_opt, pat)) =
	(* [Rule 43] *)
	let
	    val (VE1,tau1) = elabPat utaus (C, pat)
	    val (VE, tau)  =
		case ty_opt
		  of NONE    => (VE1,tau1)
		   | SOME ty =>
		     let
			 val tau = elabTy(C, ty)
		     in
			 Type.unify(tau1,tau)
			 handle Type.Unify =>
				error(I, "pattern does not match annotation");
			 (VE1,tau)
		     end
	in
	    if VIdMap.inDomain(VE, vid) then
		errorVId(I, "duplicate variable ", vid)
	    else
		( VIdMap.insert(VE, vid, (([],tau),IdStatus.v)), tau )
	end


    (* Type Expressions *)

    and elabTy(C, VARTy(I, tyvar)) =
	(* [Rule 44] *)
	let
	    val alpha = tyvar
	in
	    Type.fromTyVar alpha
	end

      | elabTy(C, RECORDTy(I, tyrow_opt, lv)) =
	(* [Rule 45] *)
	let
	    val rho = case tyrow_opt
			of NONE       => Type.emptyRow
			 | SOME tyrow => elabTyRow(C, tyrow)
	in
	    Type.fromRowType rho
	end

      | elabTy(C, CONTy(I, tyseq, longtycon, lv)) =
	(* [Rule 46] *)
	let
	    val Tyseq(I',tys) = tyseq
	    val k             = List.length tys
	    val taus          = List.map (fn ty => elabTy(C, ty)) tys
	    val (theta,VE)    =
		case Context.findLongTyCon(C, longtycon)
		  of SOME tystr => tystr
		   | NONE =>
		     errorLongTyCon(I, "unknown type constructor ", longtycon)
	in
	    TypeFcn.apply(taus, theta)  (* lv will be cloned during type application *)
	    handle TypeFcn.Apply =>
		errorLongTyCon(I, "arity mismatch at type application ",
				  longtycon)
	end

      | elabTy(C, ARROWTy(I, ty, ty', mode, lv)) =
	(* [Rule 47] *)
	let
	    val tau  = elabTy(C, ty)
	    val tau' = elabTy(C, ty')
	in
	    Type.fromFunType(tau,tau',ref mode,ref lv)
	end

      | elabTy(C, PARTy(I, ty)) =
	(* [Rule 48] *)
	let
	    val tau = elabTy(C, ty)
	in
	    tau
	end


    (* Type-expression Rows *)

    and elabTyRow(C, TyRow(I, lab, ty, tyrow_opt)) =
	(* [Rule 49] *)
	let
	    val tau = elabTy(C, ty)
	    val rho = case tyrow_opt
			of NONE       => Type.emptyRow
			 | SOME tyrow => elabTyRow(C, tyrow)
	in
	    Type.insertRow(rho, lab, tau)
	end



    (* Build tentative VE from LHSs of recursive valbind *)

    and lhsRecValBind(PLAINValBind(I, pat, exp, valbind_opt)) =
	let
	    val VE  = lhsRecValBindPat pat
	    val VE' = case valbind_opt
			of NONE         => VIdMap.empty
			 | SOME valbind => lhsRecValBind valbind
	in
	    VIdMap.unionWith #2 (VE,VE')
	end

      | lhsRecValBind(RECValBind(I, valbind)) =
	    lhsRecValBind valbind

    and lhsRecValBindPat(ATPat(I, atpat)) =
	    lhsRecValBindAtPat atpat

      | lhsRecValBindPat(CONPat(I, _, longvid, atpat)) =
	    lhsRecValBindAtPat atpat

      | lhsRecValBindPat(COLONPat(I, pat, ty)) =
	    lhsRecValBindPat pat

      | lhsRecValBindPat(ASPat(I, _, vid, ty_opt, pat)) =
	let
	    val VE = lhsRecValBindPat pat
	in
	    VIdMap.insert(VE, vid, (([], Type.guess false), IdStatus.v))
	end

    and lhsRecValBindAtPat(WILDCARDAtPat(I)) =
	    VIdMap.empty

      | lhsRecValBindAtPat(SCONAtPat(I, scon)) =
	    VIdMap.empty

      | lhsRecValBindAtPat(IDAtPat(I, _, longvid)) =
	   (case LongVId.explode longvid
	      of ([], vid) =>
	 	 VIdMap.singleton(vid, (([], Type.guess false), IdStatus.v))
	       | _ => VIdMap.empty
	   )

      | lhsRecValBindAtPat(RECORDAtPat(I, patrow_opt)) =
	   (case patrow_opt
	      of NONE        => VIdMap.empty
	       | SOME patrow => lhsRecValBindPatRow patrow
	   )

      | lhsRecValBindAtPat(PARAtPat(I, pat)) =
	    lhsRecValBindPat pat

    and lhsRecValBindPatRow(DOTSPatRow(I)) =
	    VIdMap.empty

      | lhsRecValBindPatRow(FIELDPatRow(I, lab, pat, patrow_opt)) =
	let
	    val VE = lhsRecValBindPat pat
	in
	    case patrow_opt
	      of NONE        => VE
	       | SOME patrow =>
		 let
		     val VE' = lhsRecValBindPatRow patrow
		 in
		     VIdMap.unionWith #2 (VE,VE')
		 end
	end



    (* Build tentative TE from LHSs of datbind *)

    and lhsDatBind(DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	(* [Rule 28, part 1] *)
	let
	    val (U,alphas) = tyvars tyvarseq
	    val k          = List.length alphas
	    val span       = lhsConBind conbind
	    val t          = TyName.tyname(TyCon.toString tycon, k, true, span)
	    val tau        = Type.fromConsType(List.map Type.fromTyVar alphas,t,ref Level.Unknown)
	    val TE'        = case datbind_opt
			       of NONE         => TyConMap.empty
				| SOME datbind => lhsDatBind datbind
	in
	    TyConMap.insert(TE', tycon, ((alphas,tau), VIdMap.empty))
	end

    and lhsConBind(ConBind(I, _, vid, ty_opt, conbind_opt)) =
	case conbind_opt
	  of NONE         => 1
	   | SOME conbind => 1 + lhsConBind conbind
end;
