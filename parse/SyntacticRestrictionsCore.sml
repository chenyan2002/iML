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

    (* Rename longvid *)

    val E : VId.Id VIdMap.map ref = ref VIdMap.empty
    fun getVId vid = 
      case VIdMap.find(!E, vid) of
        NONE => vid
      | SOME vid => vid
    fun putVId vid = 
      if VId.suffix vid = "" orelse VId.name vid = "_id" then
        let
          val new_vid = VId.new vid
          val _ = E := VIdMap.insert(!E, vid, new_vid)
        in
          new_vid
        end
      else (* already bind by rec *)
        getVId (VId.fromString (VId.name vid))

    fun getLongVId longvid = 
      let
        val (strids,vid) = LongVId.explode longvid
        val new_vid = getVId vid
      in
        LongVId.implode(strids,new_vid)
      end

    fun putLongVId longvid = 
      let
        val (strids,vid) = LongVId.explode longvid
        val new_vid = putVId vid
      in
        LongVId.implode(strids,new_vid)
      end

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
	    SCONAtExp(I, scon)

      | checkAtExp(C, IDAtExp(I, ops, longvid)) =
	    IDAtExp(I, ops, getLongVId longvid)

      | checkAtExp(C, RECORDAtExp(I, exprow_opt)) =
	let
	    val (labs,exprow) = case exprow_opt
			 of NONE        => (LabSet.empty, NONE)
			  | SOME exprow => let val (l,p) = checkExpRow(C, exprow)
                                          in (l, SOME p) end
	in
	    RECORDAtExp(I, exprow)
	end

      | checkAtExp(C, LETAtExp(I, dec, exp)) =
	let
	    val (E,dec) = checkDec(C, dec)
            val exp = checkExp(C plusE E, exp)
	in
	    LETAtExp(I, dec, exp)
	end

      | checkAtExp(C, PARAtExp(I, exp)) =
	let
	    val exp = checkExp(C, exp)
	in
	    PARAtExp(I, exp)
	end


    (* Expression Rows *)

    and checkExpRow(C, ExpRow(I, lab, exp, exprow_opt)) =
	let
	    val exp   = checkExp(C, exp)
	    val (labs,exprow) = case exprow_opt
			 of NONE        => (LabSet.empty, NONE)
			  | SOME exprow => let val (l,e) = checkExpRow(C, exprow)
                                          in (l, SOME e) end
	in
	    (* [Section 2.9, 1st bullet] *)
	    ((if LabSet.member(labs, lab) then
		errorLab(I, "duplicate label ", lab)
	    else
	        LabSet.add(labs, lab)),
             ExpRow(I, lab, exp, exprow))
	end


    (* Expressions *)

    and checkExp(C, ATExp(I, atexp)) =
	let
	    val atexp = checkAtExp(C, atexp)
	in
	    ATExp(I, atexp)
	end

      | checkExp(C, APPExp(I, exp, atexp)) =
	let
	    val exp = checkExp(C, exp)
	    val atexp = checkAtExp(C, atexp)
	in
	    APPExp(I, exp, atexp)
	end

      | checkExp(C, COLONExp(I, exp, ty)) =
	let
	    val exp = checkExp(C, exp)
	    val U  = checkTy ty
	in
	    COLONExp(I, exp, ty)
	end

      | checkExp(C, HANDLEExp(I, exp, match)) =
	let
	    val exp = checkExp(C, exp)
	    val match = checkMatch(C, match)
	in
	    HANDLEExp(I, exp, match)
	end

      | checkExp(C, RAISEExp(I, exp)) =
	let
	    val exp = checkExp(C, exp)
	in
	    RAISEExp(I, exp)
	end

      | checkExp(C, FNExp(I, match)) =
	let
	    val match = checkMatch(C, match)
	in
	    FNExp(I, match)
	end


    (* Matches *)

    and checkMatch(C, Match(I, mrule, match_opt)) =
	let
	    val mrule = checkMrule(C, mrule)
	    val match_opt = case match_opt
		       of NONE       => NONE
			| SOME match => SOME (checkMatch(C, match))
	in
	    Match(I, mrule, match_opt)
	end


    (* Match rules *)

    and checkMrule(C, Mrule(I, pat, exp)) =
	let
          val old = !E
	  val (VE,pat) = checkPat(C, pat)
	  val exp = checkExp(C plusVE VE, exp)
          val _ = E := old
	in
	  Mrule(I, pat, exp)
	end


    (* Declarations *)

    and checkDec(C, VALDec(I, tyvarseq, valbind)) =
	let
	    val U' = checkTyVarseq tyvarseq
	    (* Collect implicitly bound tyvars [Section 4.6] *)
	    val U  = TyVarSet.union(U',
			TyVarSet.difference(ScopeTyVars.unguardedTyVars valbind,
					    Uof C))
	    val (VE,valbind) = checkValBind(C plusU U, valbind)
	in
	    if not(TyVarSet.isEmpty(TyVarSet.intersection(Uof C, U))) then
		(* [Section 2.9, last bullet] *)
		error(I, "some type variables shadow previous ones")
	    else
		(BindingEnv.fromVE VE,
                 VALDec(I, tyvarseq, valbind))
	end

      | checkDec(C, TYPEDec(I, typbind)) =
	let
	    val (TE,typbind) = checkTypBind typbind
	in
	    (BindingEnv.fromTE TE, TYPEDec(I,typbind))
	end

      | checkDec(C, DATATYPEDec(I, datbind)) =
	let
	    val ((VE,TE),datbind) = checkDatBind datbind
	in
	    (BindingEnv.fromVEandTE(VE,TE), DATATYPEDec(I, datbind))
	end

      | checkDec(C, DATATYPE2Dec(I, tycon, longtycon)) =
	let
	    val VE = case findLongTyCon(C, longtycon)
		       of SOME VE => VE
			| NONE    => VIdMap.empty (* actually an error *)
	    val TE = TyConMap.singleton(tycon, VE)
	in
	    (BindingEnv.fromVEandTE(VE,TE), DATATYPE2Dec(I, tycon,longtycon))
	end

      | checkDec(C, ABSTYPEDec(I, datbind, dec)) =
	let
	    val ((VE,TE),datbind) = checkDatBind datbind
	    val    (E,dec)   = checkDec(C plusVEandTE (VE,TE), dec)
	in
	    (E, ABSTYPEDec(I, datbind, dec))
	end

      | checkDec(C, EXCEPTIONDec(I, exbind)) =
	let
	    val (VE,exbind) = checkExBind exbind
	in
	    (BindingEnv.fromVE VE, EXCEPTIONDec(I, exbind))
	end

      | checkDec(C, LOCALDec(I, dec1, dec2)) =
	let
	    val (E1,dec1) = checkDec(C, dec1)
	    val (E2,dec2) = checkDec(C plusE E1, dec2)
	in
	    (E2, LOCALDec(I, dec1, dec2))
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
	    (List.foldl (op plus) BindingEnv.empty Es,
             OPENDec(I, longstrids))
	end

      | checkDec(C, EMPTYDec(I)) =
	    (BindingEnv.empty, EMPTYDec(I))

      | checkDec(C, SEQDec(I, dec1, dec2)) =
	let
	    val (E1,dec1) = checkDec(C, dec1)
	    val (E2,dec2) = checkDec(C plusE E1, dec2)
	in
	    (E1 plus E2, SEQDec(I, dec1, dec2))
	end

    (* Value Bindings *)

    and checkValBind(C, PLAINValBind(I, pat, exp, valbind_opt)) =
	let
            (* Okay to reverse order? *)
	    val exp  = checkExp(C, exp)
	    val (VE,pat) = checkPat(C, pat)
	    val (VE',valbind_opt) = case valbind_opt
			of NONE         => (VIdMap.empty, NONE)
			 | SOME valbind => let val (v,p) = checkValBind(C, valbind)
                                          in (v, SOME p) end
	in
	    VIdMap.appi (fn(vid,_) =>
		if validBindVId vid then () else
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    ) VE;
	    (VIdMap.unionWithi
		(fn(vid,_,_) =>
		    (* [Section 2.9, 2nd bullet] *)
		    errorVId(I, "duplicate variable ", vid))
		(VE,VE'), 
             PLAINValBind(I, pat, exp, valbind_opt))
	end

      | checkValBind(C, RECValBind(I, valbind)) =
	let
	    val (VE1, valbind) = lhsRecValBind valbind
	    val (VE, valbind)  = checkValBind(C plusVE VE1, valbind)
	in
	    (VE, RECValBind(I, valbind))
	end


    (* Type Bindings *)

    and checkTypBind(TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
	let
	    val U1 = checkTyVarseq tyvarseq
	    val U2 = checkTy ty
	    val (TE,typbind_opt) = case typbind_opt
		       of NONE         => (TyConMap.empty, NONE)
			| SOME typbind => let val (t,p) = checkTypBind typbind
                                         in (t, SOME p) end
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* Restriction missing in the Definition! *)
		error(I, "free type variables in type binding")
	    else if TyConMap.inDomain(TE, tycon) then
		(* Syntactic restriction [Section 2.9, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
		(TyConMap.insert(TE, tycon, VIdMap.empty),
                 TypBind(I, tyvarseq, tycon, ty, typbind_opt))
	end


    (* Datatype Bindings *)

    and checkDatBind(DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	let
	    val  U1     = checkTyVarseq tyvarseq
	    val ((U2,VE),conbind) = checkConBind conbind
	    val ((VE',TE'),datbind_opt) = case datbind_opt
			     of NONE         => (( VIdMap.empty, TyConMap.empty ), NONE)
			      | SOME datbind => let val (v,p) = checkDatBind datbind
                                               in (v, SOME p) end
	in
	    if not(TyVarSet.isSubset(U2, U1)) then
		(* Restriction missing in Definition! *)
		error(I, "free type variables in datatype binding")
	    else if TyConMap.inDomain(TE', tycon) then
		(* [Section 2.9, 2nd bullet] *)
		errorTyCon(I, "duplicate type constructor ", tycon)
	    else
	    (( VIdMap.unionWithi (fn(vid,_,_) =>
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)) (VE,VE')
	    , TyConMap.insert(TE', tycon, VE)
	    ), DatBind(I, tyvarseq, tycon, conbind, datbind_opt))
	end


    (* Constructor Bindings *)

    and checkConBind(ConBind(I, ops, vid, ty_opt, conbind_opt)) =
	let
	    val  U      = case ty_opt
			    of NONE    => TyVarSet.empty
			     | SOME ty => checkTy ty
	    val ((U',VE),conbind_opt) = case conbind_opt
			    of NONE         => (( TyVarSet.empty, VIdMap.empty ), NONE)
			     | SOME conbind => let val (v,p) = checkConBind conbind
                                              in (v, SOME p) end
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate data constructor ", vid)
	    else if not(validConBindVId vid) then
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    else
		(( TyVarSet.union(U, U'), VIdMap.insert(VE, vid, IdStatus.c) ),
                 ConBind(I,ops,putVId vid,ty_opt,conbind_opt))
	end


    (* Exception Bindings *)

    and checkExBind(NEWExBind(I, ops, vid, ty_opt, exbind_opt)) =
	let
	    val U  = case ty_opt
			 of NONE    => TyVarSet.empty
			  | SOME ty => checkTy ty
	    val (VE,exbind_opt) = case exbind_opt
		       of NONE        => (VIdMap.empty, NONE)
		        | SOME exbind => let val (v,p) = checkExBind exbind
                                        in (v, SOME p) end
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else if not(validConBindVId vid) then
		(* [Section 2.9, 5th bullet] *)
		errorVId(I, "illegal rebinding of identifier ", vid)
	    else
  	        (VIdMap.insert(VE, vid, IdStatus.e),
                 NEWExBind(I,ops,putVId vid,ty_opt,exbind_opt))
	end

      | checkExBind(EQUALExBind(I, op1, vid, op2, longvid, exbind_opt)) =
	let
	    val (VE,exbind_opt) = case exbind_opt
		       of NONE        => (VIdMap.empty, NONE)
		        | SOME exbind => let val (v,p) = checkExBind exbind
                                        in (v, SOME p) end
            val new_longvid = getLongVId longvid
            val new_vid = putVId vid
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate exception constructor ", vid)
	    else
		(VIdMap.insert(VE, vid, IdStatus.e),
                 EQUALExBind(I,op1,new_vid,op2,new_longvid,exbind_opt))
	end


    (* Atomic Patterns *)

    and checkAtPat(C, WILDCARDAtPat(I)) =
	    (VIdMap.empty, WILDCARDAtPat(I))

      | checkAtPat(C, SCONAtPat(I, scon)) =
	((case scon
	   of SCon.REAL _ =>
	      (* [Section 2.9, 6th bullet] *)
	      error(I, "real constant in pattern")
	    | _ =>
	      VIdMap.empty
	), SCONAtPat(I,scon))

      | checkAtPat(C, IDAtPat(I, ops, longvid)) =
	let
	    val (strids,vid) = LongVId.explode longvid
	in
	    if List.null strids andalso
	       ( case findLongVId(C, longvid)
		   of NONE    => true
		    | SOME is => is = IdStatus.v )
	    then
		(VIdMap.singleton(vid, IdStatus.v),
                 IDAtPat(I, ops, putLongVId longvid))
	    else (* constructor *) 
		(VIdMap.empty,
                 IDAtPat(I, ops, getLongVId longvid))


	end

      | checkAtPat(C, RECORDAtPat(I, patrow_opt)) =
	let
	    val ((VE,labs), patrow_opt) = case patrow_opt
			      of NONE        => (( VIdMap.empty, LabSet.empty ), NONE)
			       | SOME patrow => let val (v,p) = checkPatRow(C, patrow)
                                               in (v, SOME p) end
	in
	    (VE, RECORDAtPat(I, patrow_opt))
	end

      | checkAtPat(C, PARAtPat(I, pat)) =
	let
	    val (VE,pat) = checkPat(C, pat)
	in
	    (VE, PARAtPat(I, pat))
	end


    (* Pattern Rows *)

    and checkPatRow(C, DOTSPatRow(I)) =
	    (( VIdMap.empty, LabSet.empty ), DOTSPatRow(I))

      | checkPatRow(C, FIELDPatRow(I, lab, pat, patrow_opt)) =
	let
	    val  (VE,pat)        = checkPat(C, pat)
	    val ((VE',labs),patrow_opt) = case patrow_opt
			       of NONE        => (( VIdMap.empty, LabSet.empty ), NONE)
				| SOME patrow => let val (v,p) = checkPatRow(C, patrow)
                                                in (v, SOME p) end
	in
	    if LabSet.member(labs, lab) then
		(* [Section 2.9, 1st bullet] *)
		errorLab(I, "duplicate label ", lab)
	    else
		(( VIdMap.unionWithi (fn(vid,_,_) =>
		    (* [Section 2.9, 2nd bullet] *)
		    errorVId(I, "duplicate variable ", vid)) (VE,VE')
		, LabSet.add(labs, lab)
		), FIELDPatRow(I,lab,pat,patrow_opt))
	end


    (* Patterns *)

    and checkPat(C, ATPat(I, atpat)) =
	let
	    val (VE,atpat) = checkAtPat(C, atpat)
	in
	    (VE, ATPat(I, atpat))
	end

      | checkPat(C, CONPat(I, ops, longvid, atpat)) =
	let
	    val (VE,atpat) = checkAtPat(C, atpat)
	in
	    (VE, CONPat(I,ops,getLongVId longvid,atpat))
	end

      | checkPat(C, COLONPat(I, pat, ty)) =
	let
	    val (VE,pat) = checkPat(C, pat)
	    val U  = checkTy ty
	in
	    (VE, COLONPat(I,pat,ty))
	end

      | checkPat(C, ASPat(I, ops, vid, ty_opt, pat)) =
	let
	    val (VE,pat) = checkPat(C, pat)
	    val U  = case ty_opt
		       of NONE    => TyVarSet.empty
			| SOME ty => checkTy ty
	in
	    if VIdMap.inDomain(VE, vid) then
		(* [Section 2.9, 2nd bullet] *)
		errorVId(I, "duplicate variable ", vid)
	    else
		(VIdMap.insert(VE, vid, IdStatus.v), ASPat(I,ops,putVId vid,ty_opt,pat))
	end


    (* Type Expressions *)

    and checkTy(VARTy(I, tyvar)) =
	    TyVarSet.singleton tyvar

      | checkTy(RECORDTy(I, tyrow_opt,_)) =
	let
	    val (U,labs) = case tyrow_opt
			     of NONE       => ( TyVarSet.empty, LabSet.empty )
			      | SOME tyrow => checkTyRow tyrow
	in
	    U
	end

      | checkTy(CONTy(I, tyseq, longtycon,_)) =
	let
	    val Tyseq(_,tys) = tyseq
	    val Us = List.map checkTy tys
	in
	    List.foldl TyVarSet.union TyVarSet.empty Us
	end

      | checkTy(ARROWTy(I, ty, ty',_,_)) =
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
	    val (VE,pat)  = lhsRecValBindPat pat
	    val (VE',valbind_opt) = case valbind_opt
			of NONE         => (VIdMap.empty, NONE)
			 | SOME valbind => let val (v,p) = lhsRecValBind valbind
                                          in (v, SOME p) end
	in
	    (case exp
	      of FNExp _ => VIdMap.unionWith #2 (VE,VE')
	       | _ =>
		(* [Section 2.9, 4th bullet] *)
		error(I, "illegal expression within recursive value binding"),
             PLAINValBind(I, pat, exp, valbind_opt))
	end

      | lhsRecValBind(RECValBind(I, valbind)) =
	    let val (V,valbind) = lhsRecValBind valbind
            in (V, RECValBind(I, valbind)) end

    and lhsRecValBindPat(ATPat(I, atpat)) =
	    let val (V,atpat) = lhsRecValBindAtPat atpat
            in (V, ATPat(I, atpat)) end

      | lhsRecValBindPat(CONPat(I, ops, longvid, atpat)) =
	    let val (V,atpat) = lhsRecValBindAtPat atpat
            in (V, CONPat(I, ops, longvid, atpat)) end

      | lhsRecValBindPat(COLONPat(I, pat, ty)) =
	    let val (V,pat) = lhsRecValBindPat pat
            in (V, COLONPat(I, pat, ty)) end

      | lhsRecValBindPat(ASPat(I, ops, vid, ty_opt, pat)) =
        let
          val (V,pat) = lhsRecValBindPat pat
        in
	    (VIdMap.insert(V, vid, IdStatus.v),
             ASPat(I, ops, putVId vid, ty_opt, pat))
        end

    and lhsRecValBindAtPat(WILDCARDAtPat(I)) =
	    (VIdMap.empty, WILDCARDAtPat(I))

      | lhsRecValBindAtPat(SCONAtPat(I, scon)) =
	    (VIdMap.empty, SCONAtPat(I, scon))

      | lhsRecValBindAtPat(IDAtPat(I, ops, longvid)) =
	   ((case LongVId.explode longvid
	      of ([], vid) => VIdMap.singleton(vid, IdStatus.v)
	       | _         => VIdMap.empty
	   ), IDAtPat(I, ops, putLongVId longvid))

      | lhsRecValBindAtPat(RECORDAtPat(I, patrow_opt)) =
        let 
          val (V, patrow_opt) =	case patrow_opt
	                         of NONE        => (VIdMap.empty, NONE)
	                          | SOME patrow => let val (v,p) = lhsRecValBindPatRow patrow
                                                  in (v, SOME p) end
        in
          (V, RECORDAtPat(I, patrow_opt))
	end

      | lhsRecValBindAtPat(PARAtPat(I, pat)) =
	    let val (V,pat) = lhsRecValBindPat pat
            in (V, PARAtPat(I, pat)) end

    and lhsRecValBindPatRow(DOTSPatRow(I)) =
	    (VIdMap.empty, DOTSPatRow(I))

      | lhsRecValBindPatRow(FIELDPatRow(I, lab, pat, patrow_opt)) =
	let
	    val (VE,pat)  = lhsRecValBindPat pat
            val (V, patrow_opt) = case patrow_opt
	                           of NONE        => (VE, NONE)
	                            | SOME patrow =>
                                      let
                                        val (v,p) = lhsRecValBindPatRow patrow
                                      in
		                        (VIdMap.unionWith #2 (VE, v), SOME p)
                                      end
        in
          (V, FIELDPatRow(I,lab,pat,patrow_opt))
	end
end;
