(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML syntactic restrictions for the core
 *
 * Definition, Section 2.9
 *
 * Notes:
 *   - The "syntactic restrictions" defined in the Definition are not purely
 *     syntactic. E.g. the restriction that valbinds may not bind the same vid
 *     twice [2nd bullet] cannot be checked without proper binding analysis,
 *     to compute identifier status.
 *   - Also, checking of type variable shadowing [last bullet] is a global
 *     check dependent on context. Moreover, it requires the transformation from
 *     Section 4.6 to be done first.
 *   - The Definition contains a bug -- an important syntactic restriction
 *     is missing:
 *       "Any tyvar occuring on the right side of a typbind or datbind of the
 *        form tyvarseq tycon = ... must occur in tyvarseq."
 *)

structure SyntacticRestrictionsCore : SYNTACTIC_RESTRICTIONS_CORE =
struct
    (* Import *)

    open GrammarCore
    open BindingObjectsCore
    open Error


    (* Helpers for context modification *)

    open BindingContext
    val plus = BindingEnv.plus

    infix plus plusU plusVE plusTE plusVEandTE plusE


    (* Checking restriction for vids in binding [Section 2.9, 5th bullet] *)

    fun validBindVId vid =
	    vid <> VId.fromString "true" andalso
	    vid <> VId.fromString "false" andalso
	    vid <> VId.fromString "nil" andalso
	    vid <> VId.fromString "::"  andalso
	    vid <> VId.fromString "ref"

    fun validConBindVId vid =
	    validBindVId vid andalso
	    vid <> VId.fromString "it"


    (* Type variable sequences *)

    fun checkTyVarseq(TyVarseq(I, tyvars)) =
	(* [Section 2.9, 3rd bullet; Section 3.5, 3rd bullet] *)
	let
	    fun check(U, []) = U
	      | check(U, tyvar::tyvars) =
		    if TyVarSet.member(U, tyvar) then
			errorTyVar(I, "duplicate type variable ", tyvar)
		    else
			check(TyVarSet.add(U, tyvar), tyvars)
	in
	    check(TyVarSet.empty, tyvars)
	end


    (* Atomic Expressions *)

    fun checkAtExp(C, SCONAtExp(I, scon)) =
	    ()

      | checkAtExp(C, IDAtExp(I, _, longvid)) =
	    ()

      | checkAtExp(C, RECORDAtExp(I, exprow_opt)) =
	let
	    val labs = case exprow_opt
			 of NONE        => LabSet.empty
			  | SOME exprow => checkExpRow(C, exprow)
	in
	    ()
	end

      | checkAtExp(C, LETAtExp(I, dec, exp)) =
	let
	    val E = checkDec(C, dec)
	in
	    checkExp(C plusE E, exp)
	end

      | checkAtExp(C, PARAtExp(I, exp)) =
	let
	    val () = checkExp(C, exp)
	in
	    ()
	end


    (* Expression Rows *)

    and checkExpRow(C, ExpRow(I, lab, exp, exprow_opt)) =
	let
	    val ()   = checkExp(C, exp)
	    val labs = case exprow_opt
			 of NONE        => LabSet.empty
			  | SOME exprow => checkExpRow(C, exprow)
	in
	    (* [Section 2.9, 1st bullet] *)
	    if LabSet.member(labs, lab) then
		errorLab(I, "duplicate label ", lab)
	    else
		LabSet.add(labs, lab)
	end


    (* Expressions *)

    and checkExp(C, ATExp(I, atexp)) =
	let
	    val () = checkAtExp(C, atexp)
	in
	    ()
	end

      | checkExp(C, APPExp(I, exp, atexp)) =
	let
	    val () = checkExp(C, exp)
	    val () = checkAtExp(C, atexp)
	in
	    ()
	end

      | checkExp(C, COLONExp(I, exp, ty)) =
	let
	    val () = checkExp(C, exp)
	    val U  = checkTy ty
	in
	    ()
	end

      | checkExp(C, HANDLEExp(I, exp, match)) =
	let
	    val () = checkExp(C, exp)
	    val () = checkMatch(C, match)
	in
	    ()
	end

      | checkExp(C, RAISEExp(I, exp)) =
	let
	    val () = checkExp(C, exp)
	in
	    ()
	end

      | checkExp(C, FNExp(I, match)) =
	let
	    val () = checkMatch(C, match)
	in
	    ()
	end


    (* Matches *)

    and checkMatch(C, Match(I, mrule, match_opt)) =
	let
	    val () = checkMrule(C, mrule)
	    val () = case match_opt
		       of NONE       => ()
			| SOME match => checkMatch(C, match)
	in
	    ()
	end


    (* Match rules *)

    and checkMrule(C, Mrule(I, pat, exp)) =
	let
	    val VE = checkPat(C, pat)
	    val () = checkExp(C plusVE VE, exp)
	in
	    ()
	end


    (* Declarations *)

    and checkDec(C, VALDec(I, tyvarseq, valbind)) =
	let
	    val U' = checkTyVarseq tyvarseq
	    (* Collect implicitly bound tyvars [Section 4.6] *)
	    val U  = TyVarSet.union(U',
			TyVarSet.difference(ScopeTyVars.unguardedTyVars valbind,
					    Uof C))
	    val VE = checkValBind(C plusU U, valbind)
	in
	    if not(TyVarSet.isEmpty(TyVarSet.intersection(Uof C, U))) then
		(* [Section 2.9, last bullet] *)
		error(I, "some type variables shadow previous ones")
	    else
		BindingEnv.fromVE VE
	end

      | checkDec(C, TYPEDec(I, typbind)) =
	let
	    val TE = checkTypBind typbind
	in
	    BindingEnv.fromTE TE
	end

      | checkDec(C, DATATYPEDec(I, datbind)) =
	let
	    val (VE,TE) = checkDatBind datbind
	in
	    BindingEnv.fromVEandTE(VE,TE)
	end

      | checkDec(C, DATATYPE2Dec(I, tycon, longtycon)) =
	let
	    val VE = case findLongTyCon(C, longtycon)
		       of SOME VE => VE
			| NONE    => VIdMap.empty (* actually an error *)
	    val TE = TyConMap.singleton(tycon, VE)
	in
	    BindingEnv.fromVEandTE(VE,TE)
	end

      | checkDec(C, ABSTYPEDec(I, datbind, dec)) =
	let
	    val (VE,TE) = checkDatBind datbind
	    val    E    = checkDec(C plusVEandTE (VE,TE), dec)
	in
	    E
	end

      | checkDec(C, EXCEPTIONDec(I, exbind)) =
	let
	    val VE = checkExBind exbind
	in
	    BindingEnv.fromVE VE
	end

      | checkDec(C, LOCALDec(I, dec1, dec2)) =
	let
	    val E1 = checkDec(C, dec1)
	    val E2 = checkDec(C plusE E1, dec2)
	in
	    E2
	end

      | checkDec(C, OPENDec(I, longstrids)) =
	let
	    val Es =
		List.map
		    (fn longstrid =>
			case findLongStrId(C, longstrid)
			  of SOME E => E
			   | NONE => BindingEnv.empty) (* actually an error *)
		    longstrids
	in
	    List.foldl (op plus) BindingEnv.empty Es
	end

      | checkDec(C, EMPTYDec(I)) =
	    BindingEnv.empty

      | checkDec(C, SEQDec(I, dec1, dec2)) =
	let
	    val E1 = checkDec(C, dec1)
	    val E2 = checkDec(C plusE E1, dec2)
	in
	    E1 plus E2
	end


    (* Value Bindings *)

    and checkValBind(C, PLAINValBind(I, pat, exp, valbind_opt)) =
	let
	    val VE  = checkPat(C, pat)
	    val ()  = checkExp(C, exp)
	    val VE' = case valbind_opt
			of NONE         => VIdMap.empty
			 | SOME valbind => checkValBind(C, valbind)
	in
	    VIdMap.appi (fn(vid,_) =>
		if validBindVId vid then () else
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    ) VE;
	    VIdMap.unionWithi
		(fn(vid,_,_) =>
		    (* [Section 2.9, 2nd bullet] *)
		    errorVId(I, "duplicate variable ", vid))
		(VE,VE')
	end

      | checkValBind(C, RECValBind(I, valbind)) =
	let
	    val VE1 = lhsRecValBind valbind
	    val VE  = checkValBind(C plusVE VE1, valbind)
	in
	    VE
	end


    (* Type Bindings *)

    and checkTypBind(TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
	let
	    val U1 = checkTyVarseq tyvarseq
	    val U2 = checkTy ty
	    val TE = case typbind_opt
		       of NONE         => TyConMap.empty
			| SOME typbind => checkTypBind typbind
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* Restriction missing in the Definition! *)
		error(I, "free type variables in type binding")
	    else if TyConMap.inDomain(TE, tycon) then
		(* Syntactic restriction [Section 2.9, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
		TyConMap.insert(TE, tycon, VIdMap.empty)
	end


    (* Datatype Bindings *)

    and checkDatBind(DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	let
	    val  U1     = checkTyVarseq tyvarseq
	    val (U2,VE) = checkConBind conbind
	    val(VE',TE') = case datbind_opt
			     of NONE         => ( VIdMap.empty, TyConMap.empty )
			      | SOME datbind => checkDatBind datbind
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* Restriction missing in Definition! *)
		error(I, "free type variables in datatype binding")
	    else if TyConMap.inDomain(TE', tycon) then
		(* [Section 2.9, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
	    ( VIdMap.unionWithi (fn(vid,_,_) =>
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)) (VE,VE')
	    , TyConMap.insert(TE', tycon, VE)
	    )
	end


    (* Constructor Bindings *)

    and checkConBind(ConBind(I, _, vid, ty_opt, conbind_opt)) =
	let
	    val  U      = case ty_opt
			    of NONE    => TyVarSet.empty
			     | SOME ty => checkTy ty
	    val (U',VE) = case conbind_opt
			    of NONE         => ( TyVarSet.empty, VIdMap.empty )
			     | SOME conbind => checkConBind conbind
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)
	    else if not(validConBindVId vid) then
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    else
		( TyVarSet.union(U, U'), VIdMap.insert(VE, vid, IdStatus.c) )
	end


    (* Exception Bindings *)

    and checkExBind(NEWExBind(I, _, vid, ty_opt, exbind_opt)) =
	let
	    val U  = case ty_opt
			 of NONE    => TyVarSet.empty
			  | SOME ty => checkTy ty
	    val VE = case exbind_opt
		       of NONE        => VIdMap.empty
		        | SOME exbind => checkExBind exbind
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else if not(validConBindVId vid) then
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    else
		VIdMap.insert(VE, vid, IdStatus.e)
	end

      | checkExBind(EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
	let
	    val VE = case exbind_opt
		       of NONE        => VIdMap.empty
		        | SOME exbind => checkExBind exbind
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else
		VIdMap.insert(VE, vid, IdStatus.e)
	end


    (* Atomic Patterns *)

    and checkAtPat(C, WILDCARDAtPat(I)) =
	    VIdMap.empty

      | checkAtPat(C, SCONAtPat(I, scon)) =
	(case scon
	   of SCon.REAL _ =>
	      (* [Section 2.9, 6th bullet] *)
	      error(I, "real constant in pattern")
	    | _ =>
	      VIdMap.empty
	)

      | checkAtPat(C, IDAtPat(I, _, longvid)) =
	let
	    val (strids,vid) = LongVId.explode longvid
	in
	    if List.null strids andalso
	       ( case findLongVId(C, longvid)
		   of NONE    => true
		    | SOME is => is = IdStatus.v )
	    then
		VIdMap.singleton(vid, IdStatus.v)
	    else
		VIdMap.empty
	end

      | checkAtPat(C, RECORDAtPat(I, patrow_opt)) =
	let
	    val (VE,labs) = case patrow_opt
			      of NONE        => ( VIdMap.empty, LabSet.empty )
			       | SOME patrow => checkPatRow(C, patrow)
	in
	    VE
	end

      | checkAtPat(C, PARAtPat(I, pat)) =
	let
	    val VE = checkPat(C, pat)
	in
	    VE
	end


    (* Pattern Rows *)

    and checkPatRow(C, DOTSPatRow(I)) =
	    ( VIdMap.empty, LabSet.empty )

      | checkPatRow(C, FIELDPatRow(I, lab, pat, patrow_opt)) =
	let
	    val  VE        = checkPat(C, pat)
	    val (VE',labs) = case patrow_opt
			       of NONE        => ( VIdMap.empty, LabSet.empty )
				| SOME patrow => checkPatRow(C, patrow)
	in
	    if LabSet.member(labs, lab) then
		(* [Section 2.9, 1st bullet] *)
		errorLab(I, "duplicate label ", lab)
	    else
		( VIdMap.unionWithi (fn(vid,_,_) =>
		    (* [Section 2.9, 2nd bullet] *)
		    errorVId(I, "duplicate variable ", vid)) (VE,VE')
		, LabSet.add(labs, lab)
		)
	end


    (* Patterns *)

    and checkPat(C, ATPat(I, atpat)) =
	let
	    val VE = checkAtPat(C, atpat)
	in
	    VE
	end

      | checkPat(C, CONPat(I, _, longvid, atpat)) =
	let
	    val VE = checkAtPat(C, atpat)
	in
	    VE
	end

      | checkPat(C, COLONPat(I, pat, ty)) =
	let
	    val VE = checkPat(C, pat)
	    val U  = checkTy ty
	in
	    VE
	end

      | checkPat(C, ASPat(I, _, vid, ty_opt, pat)) =
	let
	    val VE = checkPat(C, pat)
	    val U  = case ty_opt
		       of NONE    => TyVarSet.empty
			| SOME ty => checkTy ty
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate variable ", vid)
	    else
		VIdMap.insert(VE, vid, IdStatus.v)
	end


    (* Type Expressions *)

    and checkTy(VARTy(I, tyvar)) =
	    TyVarSet.singleton tyvar

      | checkTy(RECORDTy(I, tyrow_opt)) =
	let
	    val (U,labs) = case tyrow_opt
			     of NONE       => ( TyVarSet.empty, LabSet.empty )
			      | SOME tyrow => checkTyRow tyrow
	in
	    U
	end

      | checkTy(CONTy(I, tyseq, longtycon)) =
	let
	    val Tyseq(_,tys) = tyseq
	    val Us = List.map checkTy tys
	in
	    List.foldl TyVarSet.union TyVarSet.empty Us
	end

      | checkTy(ARROWTy(I, ty, ty')) =
	let
	    val U  = checkTy ty
	    val U' = checkTy ty'
	in
	    TyVarSet.union(U, U')
	end

      | checkTy(PARTy(I, ty)) =
	let
	    val U = checkTy ty
	in
	    U
	end


    (* Type-expression Rows *)

    and checkTyRow(TyRow(I, lab, ty, tyrow_opt)) =
	let
	    val  U        = checkTy ty
	    val (U',labs) = case tyrow_opt
			      of NONE       => ( TyVarSet.empty, LabSet.empty )
			       | SOME tyrow => checkTyRow tyrow
	in
	    if LabSet.member(labs, lab) then
		(* [Section 2.9, 1st bullet] *)
		errorLab(I, "duplicate label ", lab)
	    else
		( TyVarSet.union(U, U'), LabSet.add(labs, lab) )
	end



    (* Build tentative VE from LHSs of recursive valbind *)

    and lhsRecValBind(PLAINValBind(I, pat, exp, valbind_opt)) =
	let
	    val VE  = lhsRecValBindPat pat
	    val VE' = case valbind_opt
			of NONE         => VIdMap.empty
			 | SOME valbind => lhsRecValBind valbind
	in
	    case exp
	      of FNExp _ => VIdMap.unionWith #2 (VE,VE')
	       | _ =>
		(* [Section 2.9, 4th bullet] *)
		error(I, "illegal expression within recursive value binding")
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
	    VIdMap.insert(lhsRecValBindPat pat, vid, IdStatus.v)

    and lhsRecValBindAtPat(WILDCARDAtPat(I)) =
	    VIdMap.empty

      | lhsRecValBindAtPat(SCONAtPat(I, scon)) =
	    VIdMap.empty

      | lhsRecValBindAtPat(IDAtPat(I, _, longvid)) =
	   (case LongVId.explode longvid
	      of ([], vid) => VIdMap.singleton(vid, IdStatus.v)
	       | _         => VIdMap.empty
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
	    val VE  = lhsRecValBindPat pat
	in
	    case patrow_opt
	      of NONE        => VE
	       | SOME patrow =>
		 VIdMap.unionWith #2 (VE, lhsRecValBindPatRow patrow)
	end
end;
