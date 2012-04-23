(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML signatures
 *
 * Definition, Sections 5.1, 5.3, and 5.6
 *)

structure Sig :> SIG =
struct
    (* Import *)

    open StaticObjectsCore
    open StaticObjectsModule

    type Realisation = Type.Realisation


    (* Type variable and type name extraction [Section 4.2] *)

    fun tyvars (T,E)       = StaticEnv.tyvars E
    fun tynames (T,E)      = TyNameSet.difference(StaticEnv.tynames E, T)
    fun undetermined (T,E) = StaticEnv.undetermined E


    (* Alpha Renaming *)

    fun rename (T,E) =
	let
	    val phi' = TyNameSet.foldl
			 (fn(t,phi')=> TyNameMap.insert(phi',t,TyName.rename t))
			 TyNameMap.empty T
	    val phi = TyNameMap.map (TypeFcn.rename o TypeFcn.fromTyName) phi'
	    val T'  = TyNameSet.map (fn t => valOf(TyNameMap.find(phi',t))) T
	    val E'  = StaticEnv.realise phi E
	in
	    (T',E')
	end


    (* Matching [Section 5.6] *)

    exception Match

    fun matchTheta(theta', theta, phi, T) =
	if TypeFcn.arity theta <> TypeFcn.arity theta' then
	    raise Match
	else
	case TypeFcn.toTyName theta
	  of NONE   => phi
	   | SOME t =>
		if not(TyNameSet.member(T, t))
		orelse TyNameMap.inDomain(phi, t) then
		    phi
		else if TyName.admitsEquality t
		andalso not(TypeFcn.admitsEquality theta') then
		    raise Match
		else
		let
		    val phi' = TyNameMap.insert(phi, t, TypeFcn.rename theta')
		in
		    TyNameMap.map (TypeFcn.realise phi') phi'
		end

    fun matchTE(TE', TE, phi, T) =
	let
	    fun matchTyStr(tycon, (theta,VE), phi) =
		case TyConMap.find(TE', tycon)
		  of NONE             => raise Match
		   | SOME(theta',VE') => matchTheta(theta', theta, phi, T)
	in
	    TyConMap.foldli matchTyStr phi TE
	end

    fun matchSE(SE', SE, phi, T) =
	let
	    fun matchStr(strid, E, phi) =
		case StrIdMap.find(SE', strid)
		  of NONE    => raise Match
		   | SOME E' => matchE(E', E, phi, T)
	in
	    StrIdMap.foldli matchStr phi SE
	end

    and matchE(Env(SE',TE',VE',BE'), Env(SE,TE,VE,BE), phi, T) =
	let
	    val phi1 = matchTE(TE', TE, phi, T)
	    val phi2 = matchSE(SE', SE, phi1, T)
	in
	    phi2
	end

    fun match(E', (T,E)) =
	let
	    val phi    = matchE(E', E, TyNameMap.empty, T)
	    val Eminus = StaticEnv.realise phi E
	in
	    if StaticEnv.enriches(E',Eminus) then
		(Eminus, phi)
	    else
		raise Match
	end
end;
