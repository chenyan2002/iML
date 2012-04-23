(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML environments of the static semantics of the core
 *
 * Definition, Sections 4.2, 4.3, 4.8, 4.9, and 5.5
 *
 * Note:
 *     We call the domain type of value environments ValStr.
 *)

structure StaticEnv :> STATIC_ENV =
struct
    (* Inheritance *)

    structure GenericEnv = NGenericEnvFn(open StaticObjectsCore
					 fun unEnv(Env E) = E)
    open GenericEnv


    (* Import *)

    open StaticObjectsCore

    type Realisation = Type.Realisation


    (* Further modifications [Section 4.3] *)

    infix TEplus

    fun TE' TEplus (Env(SE,TE,VE,BE)) = Env(SE, TyConMap.unionWith #2 (TE',TE), VE,BE)


    (* Type variable and type name set [Section 4.2] *)

    fun collect (empty, union, collectTypeScheme, collectTypeFcn) =
	let
	    fun collectVE(VE : ValEnv) =
		VIdMap.foldl
		    (fn((sigma,is), S) => union(S, collectTypeScheme sigma))
		    empty VE

	    fun collectTE(TE : TyEnv) =
		TyConMap.foldl
		    (fn((theta,VE), S) => union(union(S, collectTypeFcn theta),
						collectVE VE)) empty TE
	    fun collectSE(SE : StrEnv) =
		StrIdMap.foldl (fn(E, S) => union(S, collect E)) empty SE

	    and collect(Env(SE,TE,VE,BE)) =
		union(union(collectSE SE, collectTE TE), collectVE VE)
	in
	    (collect, collectSE, collectTE, collectVE)
	end

    val (tyvars, tyvarsSE, tyvarsTE, tyvarsVE) =
	collect(TyVarSet.empty, TyVarSet.union,
		TypeScheme.tyvars, TypeFcn.tyvars)
    val (tynames, tynamesSE, tynamesTE, tynamesVE) =
	collect(TyNameSet.empty, TyNameSet.union,
		TypeScheme.tynames, TypeFcn.tynames)
    val (undetermined, _, _, _) =
	collect(StampMap.empty, StampMap.unionWith #2,
		TypeScheme.undetermined, TypeFcn.undetermined)


    (* Well-formedness [Section 4.9] *)

    fun isWellFormedTyStr (theta,VE) =
	VIdMap.isEmpty VE orelse isSome(TypeFcn.toTyName theta)

    fun isWellFormedTE TE =
	TyConMap.all isWellFormedTyStr TE

    fun isWellFormedSE SE =
	StrIdMap.all isWellFormed SE

    and isWellFormed (Env(SE,TE,VE,BE)) =
	isWellFormedTE TE andalso isWellFormedSE SE



    (* Closure [Section 4.8] *)

    fun Clos VE =
	VIdMap.map (fn((_,tau), is) => (TypeScheme.Clos tau, is)) VE


    (* Realisation [Section 5.2] *)

    fun realiseVE phi VE =
	VIdMap.map (fn(sigma,is) => ( TypeScheme.realise phi sigma, is )) VE

    and realiseTE phi TE =
	TyConMap.map (fn(theta,VE) => ( TypeFcn.realise phi theta
				      , realiseVE phi VE
				      )) TE
    and realiseSE phi SE =
	StrIdMap.map (realise phi) SE

    and realise phi (Env(SE,TE,VE,BE)) =
	Env( realiseSE phi SE
	   , realiseTE phi TE
	   , realiseVE phi VE
           , BE
	   )


    (* Maximise equality of a type environment [Section 4.9],
     * together with its companion value environment
     *)

    fun respectsEqualityValStr ((alphas, ref(FunType(tau, _, _, _))), is) =
	    TypeFcn.admitsEquality (alphas, tau)
      | respectsEqualityValStr _ = true

    fun respectsEquality ((alphas,tau), VE) =
	let
	    val t = Type.tyname tau
	in
	    if TyName.admitsEquality t then
		TyName.toString t = "ref" orelse
		VIdMap.all respectsEqualityValStr VE
	    else
		true
	end

    fun maximiseEquality(TE,VE) =
	let
	    fun checkTyStr((theta, VE), (phi, change)) =
		if respectsEquality (theta,VE) then ( phi, change ) else
		let
		    val t      = Option.valOf(TypeFcn.toTyName theta)
		    val theta' = TypeFcn.fromTyName(TyName.removeEquality t)
		in
		    ( TyNameMap.insert(phi, t, theta'), true )
		end

	    fun checkTE(TE, phi) =
		let
		    val (phi',change) = TyConMap.foldl checkTyStr (phi,false) TE
		    val TE'           = realiseTE phi' TE
		in
		    if change then checkTE(TE', phi')
			      else (TE', phi')
		end

	    val (TE',phi) = checkTE(TE, TyNameMap.empty)
	in
	    ( TE', realiseVE phi VE )
	end


    (* Abstraction of a type environment [Section 4.9] *)

    fun AbsTE(TE) = TyConMap.map (fn(theta,VE) => (theta,VIdMap.empty)) TE

    fun Abs(TE,E) =
	let
	    val ts  = TyConMap.foldl (fn((theta,VE), ts) =>
				      valOf (TypeFcn.toTyName theta)::ts) [] TE
	    val phi = List.foldl
			(fn(t,phi) => TyNameMap.insert(phi, t,
					TypeFcn.fromTyName(TyName.Abs t)))
			TyNameMap.empty ts
	in
	    realise phi (AbsTE(TE) TEplus E)
	end


    (* Disjointness *)

    fun disjoint(Env(SE1,TE1,VE1,BE1), Env(SE2,TE2,VE2,BE2)) =
	    StrIdMap.disjoint(SE1,SE2) andalso
	    TyConMap.disjoint(TE1,TE2) andalso
	    VIdMap.disjoint(VE1,VE2)


    (* Enrichment [Section 5.5] *)

    fun equalsVE(VE1,VE2) =
	VIdMap.numItems VE1 = VIdMap.numItems VE2 andalso
	VIdMap.alli
	    (fn(vid, (sigma1,is1)) =>
		case VIdMap.find(VE2, vid)
		  of NONE             => false
		   | SOME(sigma2,is2) =>
			TypeScheme.equals(sigma1,sigma2) andalso is1 = is2
	    )
	    VE1


    fun enriches(Env(SE1,TE1,VE1,BE1), Env(SE2,TE2,VE2,BE2)) =
	    enrichesSE(SE1,SE2) andalso
	    enrichesTE(TE1,TE2) andalso
	    enrichesVE(VE1,VE2)

    and enrichesSE(SE1,SE2) =
	StrIdMap.alli
	    (fn(strid, E2) =>
		case StrIdMap.find(SE1, strid)
		  of NONE    => false
		   | SOME E1 => enriches(E1,E2)
	    )
	    SE2

    and enrichesTE(TE1,TE2) =
	TyConMap.alli
	    (fn(tycon, tystr2) =>
		case TyConMap.find(TE1, tycon)
		  of NONE        => false
		   | SOME tystr1 => enrichesTyStr(tystr1,tystr2)
	    )
	    TE2

    and enrichesVE(VE1,VE2) =
	VIdMap.alli
	    (fn(vid, valstr2) =>
		case VIdMap.find(VE1, vid)
		  of NONE         => false
		   | SOME valstr1 => enrichesValStr(valstr1,valstr2)
	    )
	    VE2

    and enrichesTyStr((theta1,VE1), (theta2,VE2)) =
	    TypeFcn.equals(theta1,theta2) andalso
	    ( VIdMap.isEmpty VE2 orelse equalsVE(VE1,VE2) )

    and enrichesValStr((sigma1,is1), (sigma2,is2)) =
	    TypeScheme.generalises(sigma1,sigma2) andalso
	    IdStatus.generalises(is1,is2)
end;
