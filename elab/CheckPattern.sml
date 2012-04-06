(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML consistency of patterns and matches
 *
 * Definition, Section 4.11
 *
 * Note:
 *   - We represent special constants in a normalised form as strings.
 *   - The requirement to check for irredundancy of matches is a `bug' in the
 *     definition since this cannot be checked in general for two reasons:
 *
 *     (1) There may be (hidden) aliasing of exception constructors.
 *         Consequently, we only detect redundant exception constructors
 *         if they are denoted by the same longvid.
 *
 *     (2) There is no requirement of consistency for constructors in
 *         sharing specifications or type realisations (actually, we
 *         consider this a serious bug). For example,
 *		datatype t1 = A | B
 *		datatype t2 = C
 *		sharing type t1 = t2
 *         is a legal specification. This allows a mix of the constructors
 *         to appear in matches, rendering the terms of irredundancy and
 *         exhaustiveness meaningless. We make no attempt to detect this,
 *         so generated warnings may or may not make sense in that situation.
 *)

structure CheckPattern : CHECK_PATTERN =
struct
    (* Import *)

    type SCon    = SCon.SCon
    type Lab     = Lab.Lab
    type VId     = VId.Id
    type longVId = LongVId.longId
    type Pat     = GrammarCore.Pat
    type Match   = GrammarCore.Match
    type Env     = StaticEnv.Env

    open GrammarCore



    (*
     * Algorithm loosely based on:
     *    Peter Sestoft.
     *         "ML pattern matching compilation and partial evaluation",
     *    in: Dagstuhl Seminar on Partial Evaluation,
     *        Lecture Notes in Computer Science, Springer-Verlag 1996
     *)


    (* Value description *)

    structure SConSet'   = FinSetFn(type ord_key = string
				    val  compare = String.compare)
    structure VIdSet     = FinSetFn(type ord_key = VId.Id
				    val  compare = VId.compare)
    structure LongVIdSet = FinSetFn(type ord_key = LongVId.longId
				    val  compare = LongVId.compare)

    type SCon'         = string
    type SConSet'      = SConSet'.set
    type VIdSet        = VIdSet.set
    type LongVIdSet    = LongVIdSet.set
    type 'a LabMap     = 'a LabMap.map

    datatype description =
	  ANY
	| SCON      of SCon'
	| NOT_SCON  of SConSet'
	| EXCON     of longVId * description option
	| NOT_EXCON of LongVIdSet
	| CON       of VId * description option
	| NOT_CON   of VIdSet
	| RECORD    of description LabMap

    datatype context =
	  EXCON'  of context * longVId
	| CON'    of context * VId
	| RECORD' of context * description LabMap * Lab * PatRow option
	| MATCH'  of Source.info * Match option

    (* Normalise special constants *)

    fun normalise(SCon.INT(b, sc, ref t_opt)) =
	  Library.intToString(Library.intFromString(b, sc, t_opt))
      | normalise(SCon.WORD(b, sc, ref t_opt)) =
	  Library.wordToString(Library.wordFromString(b, sc, t_opt))
      | normalise(SCon.CHAR(sc, ref t_opt)) =
	  Library.charToString(Library.charFromString(sc, t_opt))
      | normalise(SCon.STRING(sc, ref t_opt)) =
	  Library.stringToString(Library.stringFromString(sc, t_opt))
      | normalise(SCon.REAL(sc, ref t_opt)) =
	  Library.realToString(Library.realFromString(sc, t_opt))

    fun span scon = case SCon.tyname scon of NONE   => 0
					   | SOME t => Library.span t


    (* Result type for static matching *)

    structure RegionSet = FinSetFn(type ord_key = Source.info
				   val compare  = Source.compare)

    type sets = {matches : RegionSet.set, reached : RegionSet.set}

    type result = sets * bool

    val emptySets = {matches = RegionSet.empty, reached = RegionSet.empty}

    fun update({matches, reached}, l, f) =
	let
	    val m = ref matches
	    val r = ref reached
	    val sets = {matches = m, reached = r}
	    val r = l sets
	in
	    r := f(!r);
	    {matches = !m, reached = !r}
	end

    fun extend(sets, l, I) =
	    update(sets, l, fn R => RegionSet.add(R, I))

    fun branch((sets1, exhaustive1) : result, (sets2, exhaustive2) : result) =
	    ( {matches = RegionSet.union(#matches sets1, #matches sets2),
	       reached = RegionSet.union(#reached sets1, #reached sets2)},
	     exhaustive1 andalso exhaustive2 )


    (* Static pattern matching *)

    fun matchMatch(E, desc, Match(_, mrule, match_opt), sets) =
	    matchMrule(E, desc, mrule, match_opt, sets)


    and matchMrule(E, desc, Mrule(I, pat, exp), match_opt, sets) =
	    matchPat(E, desc, pat, MATCH'(I, match_opt),
		     extend(sets, #matches, I))


    and matchAtPat(E, desc, atpat, context, sets) =
	case atpat
	  of WILDCARDAtPat(_) =>
		succeed(E, desc, context, sets)

	   | SCONAtPat(_, scon) =>
		matchSCon(E, desc, normalise scon, span scon, context, sets)

	   | IDAtPat(_, _, longvid) =>
	       (case StaticEnv.findLongVId(E, longvid)
		  of NONE =>
			succeed(E, desc, context, sets)

		   | SOME(sigma, IdStatus.v) =>
			succeed(E, desc, context, sets)

		   | SOME(sigma, IdStatus.e) =>
			matchExCon(E, desc, longvid, NONE, context, sets)

		   | SOME((_,tau), IdStatus.c) =>
		     let
			val vid  = LongVId.toId longvid
			val span = TyName.span(Type.tyname(Type.range tau))
		     in
			matchCon(E, desc, vid, span, NONE, context, sets)
		     end
	       )

	   | RECORDAtPat(_, patrow_opt) =>
		matchPatRowOpt(E, desc, patrow_opt, context, sets)

	   | PARAtPat(_, pat) =>
		matchPat(E, desc, pat, context, sets)


    and matchPat(E, desc, pat, context, sets) =
	case pat
	  of ATPat(_, atpat) =>
		matchAtPat(E, desc, atpat, context, sets)

	   | CONPat(_, _, longvid, atpat) =>
	       (case StaticEnv.findLongVId(E, longvid)
		  of SOME(sigma, IdStatus.e) =>
			matchExCon(E, desc, longvid, SOME atpat, context, sets)

		   | SOME((_,tau), IdStatus.c) =>
		     let
			val vid  = LongVId.toId longvid
			val span = TyName.span(Type.tyname(Type.range tau))
		     in
			matchCon(E, desc, vid, span, SOME atpat, context, sets)
		     end

		   | _ => raise Fail "CheckPattern.matchPat: \
				     \invalid constructed pattern"
	       )

	  | COLONPat(_, pat, ty) =>
		matchPat(E, desc, pat, context, sets)

	  | ASPat(I, _, _, _, pat) =>
		matchPat(E, desc, pat, context, sets)


    and matchPatRowOpt(E, desc, patrow_opt, context, sets) =
	let
	    val descs = case desc
			  of ANY          => LabMap.empty
			   | RECORD descs => descs
			   | _ => raise Fail "CheckPattern.matchAtPat: \
					     \invalid record pattern"
	in
	    case patrow_opt
	      of SOME(FIELDPatRow(_, lab, pat, patrow_opt')) =>
		 let
		     val desc' = case LabMap.find(descs, lab)
				   of NONE       => ANY
				    | SOME desc' => desc'
		 in
		     matchPat(E, desc', pat,
			      RECORD'(context, descs, lab, patrow_opt'), sets)
		 end

	       | _ =>
		 succeed(E, RECORD(descs), context, sets)
	end


    and matchSCon(E, desc, scon, span, context, sets) =
	let
	    val descSucc       = SCON scon
	    fun descFail scons = NOT_SCON(SConSet'.add(scons, scon))
	in
	    case desc
	      of ANY =>
		 branch(succeed(E, descSucc, context, sets),
			fail(E, descFail SConSet'.empty, context, sets)
		       )

	       | SCON scon' =>
		 if scon = scon' then
		     succeed(E, desc, context, sets)
		 else
		     fail(E, desc, context, sets)

	       | NOT_SCON scons =>
		 if SConSet'.member(scons, scon) then
		     fail(E, desc, context, sets)
		 else if SConSet'.numItems scons = span - 1 then
		     succeed(E, descSucc, context, sets)
		 else
		     branch(succeed(E, descSucc, context, sets),
			    fail(E, descFail scons, context, sets)
			   )

	       | _ => raise Fail "CheckPattern.matchSCon: type error"
	end


    and matchExCon(E, desc, longvid, atpat_opt, context, sets) =
	let
	    val context' = EXCON'(context, longvid)
	    val descSucc = EXCON(longvid, NONE)
	    fun descFail longvids =
		NOT_EXCON(LongVIdSet.add(longvids, longvid))
	in
	    case desc
	      of ANY =>
		 branch(matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
				    context, context', sets),
			fail(E, descFail LongVIdSet.empty, context, sets)
		       )

	       | EXCON(longvid', desc_opt) =>
		 if longvid = longvid' then
		     matchArgOpt(E, descSucc, desc_opt, atpat_opt,
				 context, context', sets)
		 else
		     fail(E, desc, context, sets)

	       | NOT_EXCON longvids =>
		 if LongVIdSet.member(longvids, longvid) then
		     fail(E, desc, context, sets)
		 else
		     branch(matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
					context, context', sets),
			    fail(E, descFail longvids, context, sets)
			   )

	       | _ => raise Fail "CheckPattern.matchExCon: type error"
	end


    and matchCon(E, desc, vid, span, atpat_opt, context, sets) =
	let
	    val context'      = CON'(context, vid)
	    val descSucc      = CON(vid, NONE)
	    fun descFail vids = NOT_CON(VIdSet.add(vids, vid))
	in
	    case desc
	      of ANY =>
		 if span = 1 then
		     matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
				 context, context', sets)
		 else
		     branch(matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
					context, context', sets),
			    fail(E, descFail VIdSet.empty, context, sets)
			   )

	       | CON(vid', desc_opt) =>
		 if vid = vid' then
		     matchArgOpt(E, descSucc, desc_opt, atpat_opt,
				 context, context', sets)
		 else
		     fail(E, desc, context, sets)

	       | NOT_CON vids =>
		 if VIdSet.member(vids, vid) then
		     fail(E, desc, context, sets)
		 else if VIdSet.numItems vids = span - 1 then
		     matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
				 context, context', sets)
		 else
		     branch(matchArgOpt(E, descSucc, SOME ANY, atpat_opt,
					context, context', sets),
			    fail(E, descFail vids, context, sets)
			   )

	       | _ => raise Fail "CheckPattern.matchCon: type error"
	end


    and matchArgOpt(E, desc, desc_opt, atpat_opt, context, context', sets) =
	case atpat_opt
	  of NONE =>
		succeed(E, desc, context, sets)

	   | SOME atpat =>
		matchAtPat(E, valOf desc_opt, atpat, context', sets)


    and succeed(E, desc, EXCON'(context, longvid), sets) =
	    succeed(E, EXCON(longvid, SOME desc), context, sets)

      | succeed(E, desc, CON'(context, vid), sets) =
	    succeed(E, CON(vid, SOME desc), context, sets)

      | succeed(E, desc, RECORD'(context, descs, lab, patrow_opt), sets) =
	    matchPatRowOpt(E, RECORD(LabMap.insert(descs, lab, desc)),
			   patrow_opt, context, sets)

      | succeed(E, desc, MATCH'(I, match_opt), sets) =
	    skip(match_opt, extend(sets, #reached, I))


    and skip (SOME(Match(_, mrule, match_opt)), sets) =
	    skip(match_opt, extend(sets, #matches, infoMrule mrule))

      | skip (NONE, sets) =
	    ( sets, true )


    and fail(E, desc, EXCON'(context, longvid), sets) =
	    fail(E, EXCON(longvid, SOME desc), context, sets)

      | fail(E, desc, CON'(context, vid), sets) =
	    fail(E, CON(vid, SOME desc), context, sets)

      | fail(E, desc, RECORD'(context, descs, lab, patrow_opt), sets) =
	    fail(E, RECORD(LabMap.insert(descs, lab, desc)), context, sets)

      | fail(E, desc, MATCH'(I, SOME match), sets) =
	    matchMatch(E, desc, match, sets)

      | fail(E, desc, MATCH'(I, NONE), sets) =
	    ( sets, false )


    (* Checking matches [Section 4.11, item 2; RFC conjunctive patterns;
     *                   RFC disjunctive patterns] *)

    fun checkMatch(E, match) =
	let
	    val (sets, exhaustive) = matchMatch(E, ANY, match, emptySets)
	    val unreached = RegionSet.difference(#matches sets, #reached sets)
	in
	    RegionSet.app (fn I => Error.warning(I, "redundant match rule"))
	        unreached;
	    if exhaustive then () else
		Error.warning(infoMatch match, "match not exhaustive")
	end



    (* Checking single patterns [Section 4.11, item 3] *)

    fun checkPat(E, pat) =
	let
	    val (_, exhaustive) =
		matchPat(E, ANY, pat, MATCH'(Source.nowhere, NONE), emptySets)
	in
	    if exhaustive then () else
		Error.warning(infoPat pat, "pattern not exhaustive")
	end
end;
