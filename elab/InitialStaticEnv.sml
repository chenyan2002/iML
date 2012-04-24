(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML core view of the initial static basis
 *
 * Definition, Appendix C
 *)

structure InitialStaticEnv : INITIAL_STATIC_ENV =
struct
    (* Import *)

    open StaticObjectsCore
    open IdStatus


    (* VIds [Figure 25] *)

    val vidEq     = VId.fromString "="
    val vidAssign = VId.fromString ":="

    val vidFalse  = VId.fromString "false"
    val vidTrue   = VId.fromString "true"
    val vidNil    = VId.fromString "nil"
    val vidCons   = VId.fromString "::"
    val vidRef    = VId.fromString "ref"

    val vidMatch  = VId.fromString "Match"
    val vidBind   = VId.fromString "Bind"


    (* TyCons [Figure 24] *)

    val tyconUnit   = TyCon.fromString "unit"
    val tyconBool   = TyCon.fromString "bool"
    val tyconInt    = TyCon.fromString "int"
    val tyconWord   = TyCon.fromString "word"
    val tyconReal   = TyCon.fromString "real"
    val tyconString = TyCon.fromString "string"
    val tyconChar   = TyCon.fromString "char"
    val tyconList   = TyCon.fromString "list"
    val tyconRef    = TyCon.fromString "ref"
    val tyconExn    = TyCon.fromString "exn"


    (* TyNames [Appendix C] *)

    val tBool   = TyName.tyname(TyCon.toString tyconBool,   0, true,  2)
    val tInt    = TyName.tyname(TyCon.toString tyconInt,    0, true,  0)
    val tWord   = TyName.tyname(TyCon.toString tyconWord,   0, true,  0)
    val tReal   = TyName.tyname(TyCon.toString tyconReal,   0, false, 0)
    val tString = TyName.tyname(TyCon.toString tyconString, 0, true,  0)
    val tChar   = TyName.tyname(TyCon.toString tyconChar,   0, true,  0)
    val tList   = TyName.tyname(TyCon.toString tyconList,   1, true,  2)
    val tRef    = TyName.tyname(TyCon.toString tyconRef,    1, true,  1)
    val tExn    = TyName.tyname(TyCon.toString tyconExn,    0, false, 0)

    val T0      = TyNameSet.fromList[tBool, tInt, tWord, tReal, tString, tChar,
				     tList, tRef, tExn]


    (* Types *)

    val alpha      = TyVar.fromString "'a"
    val alphaEq    = TyVar.fromString "''a"
    val tauAlpha   = Type.fromTyVar alpha
    val tauAlphaEq = Type.fromTyVar alphaEq

    val tauUnit      = Type.fromRowType Type.emptyRow
    val tauBool      = Type.fromConsType([], tBool, ref Level.Unknown)
    val tauInt       = Type.fromConsType([], tInt, ref Level.Unknown)
    val tauWord      = Type.fromConsType([], tWord, ref Level.Unknown)
    val tauReal      = Type.fromConsType([], tReal, ref Level.Unknown)
    val tauString    = Type.fromConsType([], tString, ref Level.Unknown)
    val tauChar      = Type.fromConsType([], tChar, ref Level.Unknown)
    val tauExn       = Type.fromConsType([], tExn, ref Level.Unknown)
    val tauAlphaList = Type.fromConsType([tauAlpha], tList, ref Level.Unknown)
    val tauAlphaRef  = Type.fromConsType([tauAlpha], tRef, ref Level.Unknown)


    (* TypeSchemes [Figure 25] *)

    fun pairType(tau1,tau2) =
	Type.fromRowType(
	    Type.insertRow(Type.insertRow(Type.emptyRow, Lab.fromInt 1, tau1),
							 Lab.fromInt 2, tau2))
    val funType = Type.fromFunType

    val sigmaEq     = ([alphaEq],
		       funType(pairType(tauAlphaEq,tauAlphaEq), tauBool, ref Level.Stable, ref Level.Stable))
    val sigmaAssign = ([alpha],
		       funType(pairType(tauAlphaRef,tauAlpha), tauUnit, ref Level.Stable, ref Level.Stable))
    val sigmaFalse  = ([], tauBool)
    val sigmaTrue   = ([], tauBool)
    val sigmaNil    = ([alpha], tauAlphaList)
    val sigmaCons   = ([alpha],
		       funType(pairType(tauAlpha, tauAlphaList), tauAlphaList, ref Level.Stable, ref Level.Stable))
    val sigmaRef    = ([alpha], funType(tauAlpha, tauAlphaRef, ref Level.Stable, ref Level.Stable))

    val sigmaMatch  = ([], tauExn)
    val sigmaBind   = ([], tauExn)


    (* Value entries [Figure 25] *)

    val valstrEq     = (sigmaEq,     v, Source.nowhere)
    val valstrAssign = (sigmaAssign, v, Source.nowhere)

    val valstrFalse  = (sigmaFalse,  c, Source.nowhere)
    val valstrTrue   = (sigmaTrue,   c, Source.nowhere)
    val valstrNil    = (sigmaNil,    c, Source.nowhere)
    val valstrCons   = (sigmaCons,   c, Source.nowhere)
    val valstrRef    = (sigmaRef,    c, Source.nowhere)

    val valstrMatch  = (sigmaMatch,  e, Source.nowhere)
    val valstrBind   = (sigmaBind,   e, Source.nowhere)


    (* TypeFcns [Figure 24] *)

    val thetaUnit   = ([], tauUnit)
    val thetaBool   = ([], tauBool)
    val thetaInt    = ([], tauInt)
    val thetaWord   = ([], tauWord)
    val thetaReal   = ([], tauReal)
    val thetaString = ([], tauString)
    val thetaChar   = ([], tauChar)
    val thetaExn    = ([], tauExn)
    val thetaList   = ([alpha], tauAlphaList)
    val thetaRef    = ([alpha], tauAlphaRef)


    (* TyStrs [Figure 25] *)

    val VEEmpty = VIdMap.empty
    val VEBool  = VIdMap.fromList[(vidFalse, valstrFalse),
				  (vidTrue,  valstrTrue)] : ValEnv
    val VEList  = VIdMap.fromList[(vidNil,   valstrNil),
				  (vidCons,  valstrCons)]
    val VERef   = VIdMap.fromList[(vidRef,   valstrRef)]

    val tystrUnit   = (thetaUnit,   VEEmpty)
    val tystrBool   = (thetaBool,   VEBool )
    val tystrInt    = (thetaInt,    VEEmpty)
    val tystrWord   = (thetaWord,   VEEmpty)
    val tystrReal   = (thetaReal,   VEEmpty)
    val tystrString = (thetaString, VEEmpty)
    val tystrChar   = (thetaChar,   VEEmpty)
    val tystrList   = (thetaList,   VEList )
    val tystrRef    = (thetaRef,    VERef  )
    val tystrExn    = (thetaExn,    VEEmpty)


    (* Environments [Appendix C] *)

    val SE0 = StrIdMap.empty

    val TE0 = TyConMap.fromList[(tyconUnit,   tystrUnit),
 				(tyconBool,   tystrBool),
 				(tyconInt,    tystrInt),
 				(tyconWord,   tystrWord),
 				(tyconReal,   tystrReal),
 				(tyconString, tystrString),
 				(tyconChar,   tystrChar),
 				(tyconList,   tystrList),
 				(tyconRef,    tystrRef),
 				(tyconExn,    tystrExn)]

    val VE0 = VIdMap.fromList  [(vidEq,     valstrEq),
				(vidAssign, valstrAssign),
				(vidRef,    valstrRef),
				(vidNil,    valstrNil),
				(vidCons,   valstrCons),
				(vidFalse,  valstrFalse),
				(vidTrue,   valstrTrue),
				(vidMatch,  valstrMatch),
				(vidBind,   valstrBind)]

    val E0 = Env(SE0,TE0,VE0)
end;
