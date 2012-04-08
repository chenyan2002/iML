(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML pretty printing of the static environment
 *)

structure PPStaticEnv : PP_STATIC_ENV =
struct
    (* Import *)

    open StaticObjectsCore
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^


    (* Simple objects *)

    fun ppVId vid     = text(VId.toString vid)
    fun ppTyCon tycon = text(TyCon.toString tycon)
    fun ppTyVar alpha = text(TyVar.toString alpha)
    fun ppStrId strid = text(StrId.toString strid)

    fun ppTyName t    = text(TyName.toString t)
    fun ppLv lv       = text(Level.toString (!lv))

    (* Environments *)

    fun ppConTypeScheme (_, ref(FunType(tau,_,mode,lv))) =
	    text "of" ^/^ PPType.ppType tau ^/^ ppLv mode ^/^ ppLv lv

      | ppConTypeScheme _ = empty


    fun ppValEnv VE =
	VIdMap.foldri
	    (fn(vid, (sigma,IdStatus.v), doc) =>
		fbox(nest(
		    hbox(
			text "val" ^/^
			ppVId vid ^/^
			text ":"
		    ) ^/^
		    PPType.ppTypeScheme sigma
		)) ^/^
		doc

	     | (vid, (sigma,_), doc) => doc
	    )
	    empty VE

    fun ppExEnv VE =
	VIdMap.foldri
	    (fn(vid, (sigma,IdStatus.e), doc) =>
		fbox(nest(
		    hbox(
			text "exception" ^/^
			ppVId vid
		    ) ^/^
		    ppConTypeScheme sigma
		)) ^/^
		doc

	     | (vid, (sigma,_), doc) => doc
	    )
	    empty VE

    fun ppConEnv VE =
	VIdMap.foldri
	    (fn(vid, (sigma,_), doc) =>
		fbox(nest(
		    ppVId vid ^/^
		    hbox(
			ppConTypeScheme sigma ^/^
			(if isEmpty doc then empty else text "|")
		    )
		)) ^/^
		doc
	    )
	    empty VE


    fun absTy(T, tycon, theta) =
	case TypeFcn.toTyName theta
	  of NONE    => NONE
	   | SOME t  => if TyName.toString t = TyCon.toString tycon
			andalso TyNameSet.member(T, t) then
			    SOME(TyName.admitsEquality t)
			else
			    NONE

    fun ppAbsTyEnv(T,TE) =
	TyConMap.foldri
	    (fn(tycon, (theta as (alphas,tau), VE), doc) =>
		if VIdMap.isEmpty VE then
		case absTy(T, tycon, theta)
		 of NONE    => doc
		  | SOME eq =>
		    fbox(nest(
			hbox(
			    text(if eq then "eqtype" else "type") ^/^
			    ppSeq ppTyVar alphas ^/^
			    ppTyCon tycon
			)
		    )) ^/^
		    doc
		else
		    doc
	    )
	    empty TE

    fun ppSynTyEnv(T,TE) =
	TyConMap.foldri
	    (fn(tycon, (theta as (alphas,tau), VE), doc) =>
		if VIdMap.isEmpty VE
		andalso not(isSome(absTy(T, tycon, theta))) then
		    fbox(nest(
			hbox(
			    text "type" ^/^
			    ppSeq ppTyVar alphas ^/^
			    ppTyCon tycon ^/^
			    text "="
			) ^/^
			PPType.ppType tau
		    )) ^/^
		    doc
		else
		    doc
	    )
	    empty TE

    fun ppDataTyEnv TE =
	TyConMap.foldri
	    (fn(tycon, ((alphas,tau),VE), doc) =>
		if VIdMap.isEmpty VE then
		    doc
		else
		    fbox(nest(
		        hbox(
			    text "datatype" ^/^
			    ppSeq ppTyVar alphas ^/^
			    ppTyCon tycon ^/^
			    text "="
			) ^/^
			abox(
			    ppConEnv VE
			)
		    )) ^/^
		    doc
	    )
	    empty TE

    fun ppTyEnv(T,TE) =
	    vbox(
		ppAbsTyEnv(T,TE) ^/^
		ppSynTyEnv(T,TE) ^/^
		ppDataTyEnv TE
	    )

    fun ppStrEnv(T,SE) =
	StrIdMap.foldri
	    (fn(strid, E, doc) =>
		fbox(nest(
		    hbox(
			text "structure" ^/^
			ppStrId strid ^/^
			text ":"
		    ) ^/^
		    ppSig' false (T,E)
		)) ^/^
		doc
	    )
	    empty SE

    and ppEnv'(T, Env(SE,TE,VE)) =
	    vbox(
		ppStrEnv(T,SE) ^/^
		ppTyEnv(T,TE) ^/^
		ppExEnv VE ^/^
		ppValEnv VE
	    )

    and ppEnv E = ppEnv'(TyNameSet.empty, E)


    (* Signatures *)

    and ppTyNameSet T =
	if TyNameSet.isEmpty T then
	    empty
	else
	    comment(ppCommaList ppTyName (TyNameSet.listItems T))

    and ppSig' withT (T,E) =
	    abox(below(
		nest(
		    hbox(
			text "sig" ^/^
			(if withT then ppTyNameSet T else empty)
		    ) ^/^
		    vbox(
			ppEnv'(T, E)
		    )
		) ^/^
		text "end"
	    ))

    fun ppSig Sigma = ppSig' true Sigma
end;
