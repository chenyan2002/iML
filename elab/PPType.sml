(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML pretty printing of types and type schemes
 *)

structure PPType : PP_TYPE =
struct
    (* Import *)

    open StaticObjectsCore
    open PrettyPrint
    open PPMisc

    infixr ^^ ^/^


    (* Simple objects *)

    fun ppLab lab     = text(Lab.toString lab)
    fun ppTyVar alpha = text(TyVar.toString alpha)
    fun ppTyName t    = text(TyName.toString t)
    fun ppLvVar var   = text(LvVar.toString var)
    val red = str(chr(27))^"[31m"
    val green = str(chr(27))^"[32m"
    val black = str(chr(27))^"[0m"
    fun ppLv lv       = text green ^^ text(Level.toString (!lv)) ^^ text red

    fun ppOverloadingClass O =
	let
	    val T  = OverloadingClass.set O
	    val t  = OverloadingClass.default O
	    val ts = t :: TyNameSet.listItems(TyNameSet.delete(T,t))
	in
	    brack(ppCommaList ppTyName ts)
	end


    fun ppRowVar NONE    = empty
      | ppRowVar(SOME _) = text "," ^/^ text "..."


    (* Precedences *)

    val topPrec   = 0
    val arrowPrec = 1
    val starPrec  = 2
    val applyPrec = 3
    val atomPrec  = 4

    (* Types *)

    fun ppType tau = fbox(below(nest(ppTypePrec topPrec tau))) ^^ text black

    and ppTypePrec p (ref tau')        = ppType'Prec p tau'

    and ppType'Prec p (TyVar(alpha))   = ppTyVar alpha

      | ppType'Prec p (RowType(rho,r,lv)) =
	let
	    fun isTuple(   [],     n) = n > 2
	      | isTuple(lab::labs, n) =
		    lab = Lab.fromInt n andalso isTuple(labs, n+1)

	    val labtaus     = LabMap.listItemsi rho
	    val (labs,taus) = ListPair.unzip labtaus
	in
	    if not(Option.isSome r) andalso List.null labs then
		text "unit " ^/^ ppLv lv
	    else if not(Option.isSome r) andalso isTuple(labs, 1) then
		let
		    val doc = fbox(below(nest(
				  paren(hbox(ppStarList (ppTypePrec(starPrec+1)) taus))
			      )))
		in
		    hbox(parenAt starPrec (p, doc) ^/^ ppLv lv)
		end
	    else
		hbox(brace(ppCommaList ppLabType labtaus ^^ ppRowVar r) ^^ ppLv lv)
	end

      | ppType'Prec p (FunType(tau1,tau2,mode,lv)) =
	let
	    val doc = fbox(below(nest(
			  hbox(ppTypePrec (arrowPrec+1) tau1 ^/^
			  text "->" ^/^ ppLv mode ^/^
			  ppTypePrec arrowPrec tau2 ^/^
                          ppLv lv)
		      )))
	in
	    hbox(parenAt arrowPrec (p, doc))
	end

      | ppType'Prec p (ConsType(taus,t,lv)) =
	    fbox(below(nest(
		hbox(ppSeqPrec ppTypePrec applyPrec taus ^/^ ppTyName t ^/^ ppLv lv)
	    )))

      | ppType'Prec p (Undetermined{stamp,eq,...}) =
	    text((if eq then "''" else "'") ^ Stamp.toString stamp)

      | ppType'Prec p (Overloaded(O)) =
	    text "'" ^^ ppOverloadingClass O

      | ppType'Prec p (Determined(tau)) =
	    ppTypePrec p tau

    and ppLabType(lab, tau) =
	    fbox(below(nest(
		hbox(
		    ppLab lab ^/^
		    text ":"
		) ^/^
		ppType tau
	    )))


    (* Type schemes *)

    fun ppTypeScheme sigma =
	let
	    val (alphas,tau) = TypeScheme.normalise sigma
	in
	    ppType tau
	end
end;
