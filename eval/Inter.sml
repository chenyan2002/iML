(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML interfaces
 *
 * Definition, Section 7.2
 *)

structure Inter :> INTER =
struct
    (* Import *)

    open IdsCore
    open DynamicObjectsModule


    (* Inheritance *)

    structure GenericEnv = GenericEnvFn(type Env    = Int
					type ValStr = IdStatus
					type TyStr  = ValInt
					val Env     = Int
					fun unEnv(Int I) = I)

    open DynamicObjectsCore


    (* Injections [Section 4.3] *)

    val empty		= GenericEnv.empty

    val fromSI		= GenericEnv.fromSE
    val fromTI		= GenericEnv.fromTE
    val fromVI		= GenericEnv.fromVE
    val fromVIandTI	= GenericEnv.fromVEandTE


    (* Projections [Section 4.3] *)

    val SIof		= GenericEnv.SEof
    val TIof		= GenericEnv.TEof
    val VIof		= GenericEnv.VEof


    (* Modification [Section 4.3] *)

    val plus		= GenericEnv.plus


    (* Extracting interfaces from environments [Section 7.2] *)

    fun InterVE VE = VIdMap.map (fn(v,is) => is) VE
    fun InterTE TE = TyConMap.map (fn VE => InterVE VE) TE
    fun InterSE SE = StrIdMap.map (fn E => Inter E) SE

    and Inter(Env(SE,TE,VE)) = Int(InterSE SE, InterTE TE, InterVE VE)


    (* Modification [Lookup 4.3] *)

    val findLongTyCon = GenericEnv.findLongTyCon


    (* Cutting down environments [Section 7.2] *)

    fun cutdownVE(VE, VI) =
	VIdMap.foldli
	    (fn(vid, is, VE') =>
		case VIdMap.find(VE, vid)
		  of SOME(v,is') => VIdMap.insert(VE', vid, (v,is))
		   | NONE        => VE'
	    ) VIdMap.empty VI

    fun cutdownTE(TE, TI) =
	TyConMap.foldli
	    (fn(tycon, VI', TE') =>
		case TyConMap.find(TE, tycon)
		  of SOME VE' => TyConMap.insert(TE', tycon, cutdownVE(VE',VI'))
		   | NONE     => TE'
	    ) TyConMap.empty TI

    fun cutdownSE(SE, SI) =
	StrIdMap.foldli
	    (fn(strid, I, SE') =>
		case StrIdMap.find(SE, strid)
		  of SOME E =>
		       StrIdMap.insert(SE', strid, cutdown(E,I))
		   | NONE => SE'
	    ) StrIdMap.empty SI

    and cutdown(Env(SE,TE,VE), Int(SI,TI,VI)) =
	    Env(cutdownSE(SE, SI), cutdownTE(TE, TI), cutdownVE(VE, VI))
end;
