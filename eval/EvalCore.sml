(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core evaluation
 *
 * Definition, Sections 6.7 and 6.2
 *
 * Notes:
 *   - State is passed as reference and modified via side effects. This way
 *     expanding out the state and exception convention in the inference rules
 *     can be avoided (would really be a pain). Note that the state therefore
 *     never is returned.
 *   - Doing so, we can model the exception convention using exceptions.
 *     Rules of the form A |- phrase => A'/p therefore turn into
 *     A |- phrase => A'.
 *   - We only pass the state where necessary.
 *)

structure EvalCore : EVAL_CORE =
struct
    (* Import *)

    open GrammarCore
    open DynamicObjectsCore
    open Error


    (* Helpers for environment modification *)

    val plus        = DynamicEnv.plus
    val plusVE      = DynamicEnv.plusVE
    val plusTE      = DynamicEnv.plusTE
    val plusVEandTE = DynamicEnv.plusVEandTE

    infix plus plusVE plusTE plusVEandTE


    (* Evaluating special constants [Section 6.2] *)

    fun valSCon(SCon.INT(b, sc, ref t_opt)) =
	  SVal(SVal.INT(Library.intFromString(b, sc, t_opt)))
      | valSCon(SCon.WORD(b, sc, ref t_opt)) =
	  SVal(SVal.WORD(Library.wordFromString(b, sc, t_opt)))
      | valSCon(SCon.CHAR(sc, ref t_opt)) =
	  SVal(SVal.CHAR(Library.charFromString(sc, t_opt)))
      | valSCon(SCon.STRING(sc, ref t_opt)) =
	  SVal(SVal.STRING(Library.stringFromString(sc, t_opt)))
      | valSCon(SCon.REAL(sc, ref t_opt)) =
	  SVal(SVal.REAL(Library.realFromString(sc, t_opt)))


    (* Inference rules [Section 6.7] *)

    (* Atomic Expressions *)

    fun evalAtExp(s,E, SCONAtExp(I, scon)) =
	(* [Rule 90] *)
	(valSCon scon handle Overflow =>
	    error(I, "runtime error: special constant out of range")
	)

      | evalAtExp(s,E, IDAtExp(I, _, longvid)) =
	(* [Rule 91] *)
	let
	    val (v,is) = case DynamicEnv.findLongVId(E, longvid)
			   of SOME valstr => valstr
			    | NONE =>
			      errorLongVId(I, "runtime error: \
					      \unknown identifier ", longvid)
	in
	    v
	end

      | evalAtExp(s,E, RECORDAtExp(I, exprow_opt)) =
	(* [Rule 92] *)
	let
	    val r = case exprow_opt
		      of NONE        => LabMap.empty
		       | SOME exprow => evalExpRow(s,E, exprow)
	in
	    Record r
	end

      | evalAtExp(s,E, LETAtExp(I, dec, exp)) =
	(* [Rule 93] *)
	let
	    val E' = evalDec(s,E, dec)
	    val v  = evalExp(s,E plus E', exp)
	in
	    v
	end

      | evalAtExp(s,E, PARAtExp(I, exp)) =
	(* [Rule 94] *)
	let
	    val v = evalExp(s,E, exp)
	in
	    v
	end


    (* Expression Rows *)

    and evalExpRow(s,E, ExpRow(I, lab, exp, exprow_opt)) =
	(* [Rule 95] *)
	let
	    val v = evalExp(s,E, exp)
	    val r = case exprow_opt
		      of NONE        => LabMap.empty
		       | SOME exprow => evalExpRow(s,E, exprow)
	in
	    LabMap.insert(r, lab, v)
	end


    (* Expressions *)

    and evalExp(s,E, ATExp(I, atexp)) =
	(* [Rule 96] *)
	let
	    val v = evalAtExp(s,E, atexp)
	in
	    v
	end

      | evalExp(s,E, APPExp(I, exp, atexp)) =
	(* [Rules 97 to 103] *)
	let
	    val v1 = evalExp(s,E, exp)
	    val v  = evalAtExp(s,E, atexp)
	in
	    case v1
	      of VId vid =>
		 if vid = VId.fromString "ref" then
		     (* [Rule 99] *)
		     let
		         val a = Addr.addr()
		     in
			 s := State.insertAddr(!s, a, v);
			 Addr a
		     end
		 else
		     (* [Rule 97] *)
		     VIdVal (vid,v)

	       | ExVal(ExName en) =>
		 (* [Rule 98] *)
		 ExVal(ExNameVal(en,v))

	       | Assign =>
		 (* [Rule 100] *)
		 (case Val.toPair v
		    of SOME(Addr a, v) =>
			( s := State.insertAddr(!s, a, v)
			; Record LabMap.empty
			)
		     | _ => error(I, "runtime type error: address expected")
		 )

	       | BasVal b =>
		 (* [Rule 101] *)
		 (BasVal.APPLY(b, v) handle BasVal.TypeError s =>
		     error(I, "runtime type error: " ^ s))

	       | FcnClosure(match,E',VE) =>
		 (* [Rule 102] *)
		 (let
		     val v' = evalMatch(s,E' plusVE DynamicEnv.Rec VE, v, match)
		  in
		     v'
		  end
		  handle FAIL =>
		     (* [Rule 103] *)
		     raise Pack(ExName InitialDynamicEnv.enMatch)
		 )
	       | _ =>
		 error(I, "runtime type error: applicative value expected")
	end

      | evalExp(s,E, COLONExp(I, exp, _)) =
	(* Omitted [Section 6.1] *)
	evalExp(s,E, exp)

      | evalExp(s,E, HANDLEExp(I, exp, match)) =
	(* [Rule 104 to 106] *)
	(let
	    val v = evalExp(s,E, exp)
	 in
	    (* [Rule 104] *)
	    v
	 end
	 handle Pack e =>
	    let
		val v = evalMatch(s,E,ExVal e, match)
	    in
		(* [Rule 105] *)
		v
	    end
	    handle FAIL =>
		(* [Rule 106] *)
		raise Pack e
	)

      | evalExp(s,E, RAISEExp(I, exp)) =
	(* [Rule 107] *)
	let
	    val e = case evalExp(s,E, exp)
		      of ExVal e => e
		       | _ => error(I, "runtime type error: \
				       \exception value expected")
	in
	    raise Pack e
	end

      | evalExp(s,E, FNExp(I, match)) =
	(* [Rule 108] *)
	FcnClosure(match,E,VIdMap.empty)


    (* Matches *)

    and evalMatch(s,E,v, Match(I, mrule, match_opt)) =
	(* [Rules 109 to 111] *)
	let
	    val v' = evalMrule(s,E,v, mrule)
	in
	    (* [Rule 109] *)
	    v'
	end
	handle FAIL =>
	    case match_opt
	      of NONE =>
		 (* [Rule 110] *)
		 raise FAIL

	       | SOME match =>
		 (* [Rule 111] *)
		 let
		     val v' = evalMatch(s,E,v, match)
		 in
		     v'
		 end


    (* Match rules *)

    and evalMrule(s,E,v, Mrule(I, pat, exp)) =
	(* [Rules 112 and 113] *)
	let
	    val VE = evalPat(s,E,v, pat)
	    (* [Rule 112] *)
	    val v' = evalExp(s,E plusVE VE, exp)
	in
	    v'
	end
	(* FAIL on evalPat propagates through [Rule 113] *)


    (* Declarations *)

    and evalDec(s,E, VALDec(I, tyvarseq, valbind)) =
	(* [Rule 114] *)
	let
	    val VE = evalValBind(s,E, valbind)
	in
	    DynamicEnv.fromVE VE
	end

      | evalDec(s,E, TYPEDec(I, typbind)) =
	(* [Rule 115] *)
	let
	    val TE = evalTypBind(typbind)
	in
	    DynamicEnv.fromTE TE
	end

      | evalDec(s,E, DATATYPEDec(I, datbind)) =
	(* [Rule 116] *)
	let
	    val (VE,TE) = evalDatBind(datbind)
	in
	    DynamicEnv.fromVEandTE(VE,TE)
	end

      | evalDec(s,E, DATATYPE2Dec(I, tycon, longtycon)) =
	(* [Rule 117] *)
	let
	    val VE = case DynamicEnv.findLongTyCon(E, longtycon)
		       of SOME VE => VE
			| NONE =>
			  errorLongTyCon(I, "runtime error: unknown type ",
					    longtycon)
	in
	    DynamicEnv.fromVEandTE(VE, TyConMap.singleton(tycon, VE))
	end

      | evalDec(s,E, ABSTYPEDec(I, datbind, dec)) =
	(* [Rule 118] *)
	let
	    val (VE,TE) = evalDatBind(datbind)
	    val    E'   = evalDec(s,E plusVEandTE (VE,TE), dec)
	in
	    E'
	end

      | evalDec(s,E, EXCEPTIONDec(I, exbind)) =
	(* [Rule 119] *)
	let
	    val VE = evalExBind(s,E, exbind)
	in
	    DynamicEnv.fromVE VE
	end

      | evalDec(s,E, LOCALDec(I, dec1, dec2)) =
	(* [Rule 120] *)
	let
	    val E1 = evalDec(s,E, dec1)
	    val E2 = evalDec(s,E plus E1, dec2)
	in
	    E2
	end

      | evalDec(s,E, OPENDec(I, longstrids)) =
	(* [Rule 121] *)
	let
	    val Es =
		List.map
		    (fn longstrid =>
			case DynamicEnv.findLongStrId(E, longstrid)
			  of SOME E => E
			   | NONE =>
			     errorLongStrId(I, "runtime error: unknown \
					       \structure ", longstrid) )
		    longstrids
	in
	    List.foldl DynamicEnv.plus DynamicEnv.empty Es
	end

      | evalDec(s,E, EMPTYDec(I)) =
	(* [Rule 122] *)
	DynamicEnv.empty

      | evalDec(s,E, SEQDec(I, dec1, dec2)) =
	(* [Rule 123] *)
	let
	    val E1 = evalDec(s,E, dec1)
	    val E2 = evalDec(s,E plus E1, dec2)
	in
	    E1 plus E2
	end


    (* Value Bindings *)

    and evalValBind(s,E, PLAINValBind(I, pat, exp, valbind_opt)) =
	(* [Rule 124 and 125] *)
	(let
	    val v   = evalExp(s,E, exp)
	    val VE  = evalPat(s,E,v, pat)
	    (* [Rule 124] *)
	    val VE' = case valbind_opt
			of NONE         => VIdMap.empty
			 | SOME valbind => evalValBind(s,E, valbind)
	 in
	    VIdMap.unionWith #2 (VE, VE')
	 end
	 handle FAIL =>
	    (* [Rule 125] *)
	    raise Pack(ExName InitialDynamicEnv.enBind)
	)

      | evalValBind(s,E, RECValBind(I, valbind)) =
	(* [Rule 126] *)
	let
	    val VE = evalValBind(s,E, valbind)
	in
	    DynamicEnv.Rec VE
	end


    (* Type Bindings *)

    and evalTypBind(TypBind(I, tyvarseq, tycon, ty, typbind_opt)) =
	(* [Rule 127] *)
	let
	    val TE = case typbind_opt
		       of NONE         => TyConMap.empty
			| SOME typbind => evalTypBind(typbind)
	in
	    TyConMap.insert(TE, tycon, VIdMap.empty)
	end


    (* Datatype Bindings *)

    and evalDatBind(DatBind(I, tyvarseq, tycon, conbind, datbind_opt)) =
	(* [Rule 128] *)
	let
	    val  VE       = evalConBind(conbind)
	    val (VE',TE') = case datbind_opt
			      of NONE          => ( VIdMap.empty, TyConMap.empty )
			       | SOME datbind' => evalDatBind(datbind')
	in
	    ( VIdMap.unionWith #2 (VE, VE')
	    , TyConMap.insert(TE', tycon, VE)
	    )
	end


    (* Constructor Bindings *)

    and evalConBind(ConBind(I, _, vid, _, conbind_opt)) =
	(* [Rule 129] *)
	let
	    val VE = case conbind_opt
		       of NONE         => VIdMap.empty
			| SOME conbind => evalConBind(conbind)
	in
	    VIdMap.insert(VE, vid, (VId vid,IdStatus.c))
	end


    (* Exception Bindings *)

    and evalExBind(s,E, NEWExBind(I, _, vid, _, exbind_opt)) =
	(* [Rule 130] *)
	let
	    val en = ExName.exname vid
	    val VE = case exbind_opt
		       of NONE        => VIdMap.empty
			| SOME exbind => evalExBind(s,E, exbind)
	in
	    s := State.insertExName(!s, en);
	    VIdMap.insert(VE, vid, (ExVal(ExName en),IdStatus.e))
	end

      | evalExBind(s,E, EQUALExBind(I, _, vid, _, longvid, exbind_opt)) =
	(* [Rule 131] *)
	let
	    val en = case DynamicEnv.findLongVId(E, longvid)
		       of SOME(en,IdStatus.e) => en
			| SOME _ =>
			  errorLongVId(I, "runtime error: non-exception \
					  \identifier ", longvid)
			| NONE =>
			  errorLongVId(I, "runtime error: unknown identifier ",
					  longvid)
	    val VE = case exbind_opt
		       of NONE        => VIdMap.empty
			| SOME exbind => evalExBind(s,E, exbind)
	in
	    VIdMap.insert(VE, vid, (en,IdStatus.e))
	end


    (* Atomic Patterns *)

    and evalAtPat(s,E,v, WILDCARDAtPat(I)) =
	(* [Rule 132] *)
	VIdMap.empty

      | evalAtPat(s,E,v, SCONAtPat(I, scon)) =
	(* [Rule 133 and 134] *)
	((if Val.equal(v, valSCon scon) then
	   (* [Rule 133] *)
	   VIdMap.empty
	else
	   (* [Rule 134] *)
	   raise FAIL
	) handle Overflow =>
	    error(I, "runtime error: special constant out of range")
	)

      | evalAtPat(s,E,v, IDAtPat(I, _, longvid)) =
	(* [Rule 135 to 137] *)
	let
	    val (strids,vid) = LongVId.explode longvid
	in
	    if List.null strids andalso
	       ( case DynamicEnv.findVId(E, vid)
		   of NONE       => true
		    | SOME(_,is) => is = IdStatus.v )
	    then
		(* [Rule 135] *)
		VIdMap.singleton(vid, (v,IdStatus.v))
	    else
		let
		    val (v',is) =
			case DynamicEnv.findLongVId(E, longvid)
			  of SOME valstr => valstr
			   | NONE => errorLongVId(I, "runtime error: \
						     \unknown constructor ",
						  longvid)
		in
		    if is = IdStatus.v then
			errorLongVId(I, "runtime error: non-constructor ",
					longvid)
		    else if Val.equal(v, v') then
			(* [Rule 136] *)
			VIdMap.empty
		    else
			(* [Rule 137] *)
			raise FAIL
		end
	end

      | evalAtPat(s,E,v, RECORDAtPat(I, patrow_opt)) =
	(* [Rule 138] *)
	let
	    val r  = case v
		       of Record r => r
		        | _ =>
			  error(I, "runtime type error: record expected")

	    val VE = case patrow_opt
		       of NONE        =>
			  if LabMap.isEmpty r then
			     VIdMap.empty
			  else
			     error(I, "runtime type error: \
				      \empty record expected")

			| SOME patrow =>
			      evalPatRow(s,E,r, patrow)
	in
	    VE
	end

      | evalAtPat(s,E,v, PARAtPat(I, pat)) =
	(* [Rule 139] *)
	let
	    val VE = evalPat(s,E,v, pat)
	in
	    VE
	end


    (* Pattern Rows *)

    and evalPatRow(s,E,r, DOTSPatRow(I)) =
	(* [Rule 140] *)
	VIdMap.empty

      | evalPatRow(s,E,r, FIELDPatRow(I, lab, pat, patrow_opt)) =
	(* [Rule 141 and 142] *)
	let
	    val v   = case LabMap.find(r, lab)
		        of SOME v => v
		         | _ => errorLab(I, "runtime type error: \
					    \unmatched label ", lab)
	    val VE  = evalPat(s,E,v, pat)
	    (* FAIL on evalPat propagates through [Rule 142] *)
	    (* [Rule 141] *)
	    val VE' = case patrow_opt
			of NONE        => VIdMap.empty
			 | SOME patrow => evalPatRow(s,E,r, patrow)
	in
	    VIdMap.unionWithi #2 (VE, VE')
	end


    (* Patterns *)

    and evalPat(s,E,v, ATPat(I, atpat)) =
	(* [Rule 143] *)
	let
	    val VE = evalAtPat(s,E,v, atpat)
	in
	    VE
	end

      | evalPat(s,E,v, CONPat(I, _, longvid, atpat)) =
	(* [Rules 144 to 148] *)
	let
	    val (strids,vid) = LongVId.explode longvid
	in
	    if List.null strids andalso vid = VId.fromString "ref" then
		case v
		  of Addr a =>
		     (* [Rule 148] *)
		     let
			 val v =  case State.findAddr(!s, a)
				    of SOME v => v
				     | NONE   =>
				       raise Fail "EvalCore.evalPat: \
						  \invalid address"
			 val VE = evalAtPat(s,E,v, atpat)
		     in
			 VE
		     end
		   | _ =>
			 error(I, "runtime type error: address expected")
	    else
		case DynamicEnv.findLongVId(E, longvid)
		  of SOME(VId vid, IdStatus.c) =>
		     (case v
			of VIdVal(vid',v') =>
			   if vid = vid' then
			       (* [Rule 144] *)
			       let
				   val VE = evalAtPat(s,E,v', atpat)
			       in
				   VE
			       end
			   else
			       (* [Rule 145] *)
			       raise FAIL
			 | _ =>
			       (* [Rule 145] *)
			       raise FAIL
		     )
		   | SOME(ExVal(ExName en), IdStatus.e) =>
		     (case v
			of ExVal(ExNameVal(en',v')) =>
	        	   if en = en' then
			       (* [Rule 146] *)
			       let
				   val VE = evalAtPat(s,E,v', atpat)
			       in
				   VE
			       end
			   else
			       (* [Rule 147] *)
			       raise FAIL
			 | _ =>
			       (* [Rule 147] *)
			       raise FAIL
		     )
		   | _ =>
			error(I, "runtime type error: constructor expected")
	end

      | evalPat(s,E,v, COLONPat(I, pat, _)) =
	(* Omitted [Section 6.1] *)
	evalPat(s,E,v, pat)

      | evalPat(s,E,v, ASPat(I, _, vid, _, pat)) =
	(* [Rule 149] *)
	let
	    val VE = evalPat(s,E,v, pat)
	in
	    VIdMap.insert(VE, vid, (v,IdStatus.v))
	end
end;
