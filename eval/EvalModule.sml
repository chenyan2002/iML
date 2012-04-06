(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML modules evaluation
 *
 * Definition, Section 7.3
 *
 * Notes:
 *   - State is passed as reference and modified via side effects. This way
 *     expanding out the state and exception convention in the inference rules
 *     can be avoided (would really be a pain). Note that the state therefore
 *     never is returned.
 *   - Doing so, we can model the exception convention using exceptions.
 *     Rules of the form A |- phrase => A'/p therefore turn into
 *     A |- phrase => A'.
 *   - We only pass the state where necessary, ie. strexp, strdec, strbind, and
 *     topdec (compare note in [Section 7.3]).
 *   - There is a typo in the Definition in rule 182: both occurances of IB
 *     should be replaced by B.
 *   - The rules for toplevel declarations are all wrong: in the conclusions,
 *     the result right of the arrow must be B' <+ B''> instead of B'<'> in
 *     all three rules.
 *)

structure EvalModule : EVAL_MODULE =
struct
    (* Import *)

    open GrammarModule
    open DynamicObjectsModule
    open Error

    type State = EvalCore.State


    (* Helpers for basis modification *)

    val plus    = DynamicBasis.plus
    val plusSE  = DynamicBasis.plusSE
    val plusG   = DynamicBasis.plusG
    val plusF   = DynamicBasis.plusF
    val plusE   = DynamicBasis.plusE

    infix plus plusG plusF plusE plusSE



    (* Inference rules [Section 7.3] *)


    (* Structure Expressions *)

    fun evalStrExp(s,B, STRUCTStrExp(I, strdec)) =
	(* [Rule 150] *)
	let
	    val E = evalStrDec(s,B, strdec)
	in
	    E
	end

      | evalStrExp(s,B, IDStrExp(I, longstrid)) =
	(* [Rule 151] *)
	let
	    val E = case DynamicBasis.findLongStrId(B, longstrid)
		      of SOME E => E
		       | NONE =>
			 errorLongStrId(I, "runtime error: unknown structure ",
					   longstrid)
	in
	    E
	end

      | evalStrExp(s,B, COLONStrExp(I, strexp, sigexp)) =
	(* [Rule 152] *)
	let
	    val E = evalStrExp(s,B, strexp)
	    val I = evalSigExp(IntBasis.Inter B, sigexp)
	in
	    Inter.cutdown(E, I)
	end

      | evalStrExp(s,B, SEALStrExp(_, strexp, sigexp)) =
	(* [Rule 153] *)
	let
	    val E = evalStrExp(s,B, strexp)
	    val I = evalSigExp(IntBasis.Inter B, sigexp)
	in
	    Inter.cutdown(E, I)
	end

      | evalStrExp(s,B, APPStrExp(I', funid, strexp)) =
	(* [Rule 154] *)
	let
	    val FunctorClosure((strid, I), strexp', B') =
		      case DynamicBasis.findFunId(B, funid)
			of SOME funcclos => funcclos
			 | NONE => errorFunId(I', "runtime error: \
						  \unknown functor ", funid)
	    val E  = evalStrExp(s,B, strexp)
	    val E' = evalStrExp(
			s,
			B' plusSE StrIdMap.singleton(strid, Inter.cutdown(E,I)),
			strexp')
	in
	    E'
	end

      | evalStrExp(s,B, LETStrExp(I, strdec, strexp)) =
	(* [Rule 155] *)
	let
	    val E  = evalStrDec(s,B, strdec)
	    val E' = evalStrExp(s,B plusE E, strexp)
	in
	    E'
	end


    (* Structure-level Declarations *)

    and evalStrDec(s,B, DECStrDec(I, dec)) =
	(* [Rule 156] *)
	let
	    val E' = EvalCore.evalDec(s,DynamicBasis.Eof B, dec)
	in
	    E'
	end

      | evalStrDec(s,B, STRUCTUREStrDec(I, strbind)) =
	(* [Rule 157] *)
	let
	    val SE = evalStrBind(s,B, strbind)
	in
	    DynamicEnv.fromSE SE
	end

      | evalStrDec(s,B, LOCALStrDec(I, strdec1, strdec2)) =
	(* [Rule 158] *)
	let
	    val E1 = evalStrDec(s,B, strdec1)
	    val E2 = evalStrDec(s,B plusE E1, strdec2)
	in
	    E2
	end

      | evalStrDec(s,B, EMPTYStrDec(I)) =
	(* [Rule 159] *)
	DynamicEnv.empty

      | evalStrDec(s,B, SEQStrDec(I, strdec1, strdec2)) =
	(* [Rule 160] *)
	let
	    val E1 = evalStrDec(s,B, strdec1)
	    val E2 = evalStrDec(s,B plusE E1, strdec2)
	in
	    DynamicEnv.plus(E1, E2)
	end


    (* Structure Bindings *)

    and evalStrBind(s,B, StrBind(I, strid, strexp, strbind_opt)) =
	(* [Rule 161] *)
	let
	    val E  = evalStrExp(s,B, strexp)
	    val SE = case strbind_opt
		       of NONE         => StrIdMap.empty
		        | SOME strbind => evalStrBind(s,B, strbind)
	in
	    StrIdMap.insert(SE, strid, E)
	end


    (* Signature Expressions *)

    and evalSigExp(IB, SIGSigExp(I, spec)) =
	(* [Rule 162] *)
	let
	    val I = evalSpec(IB, spec)
	in
	    I
	end

      | evalSigExp(IB, IDSigExp(I, sigid)) =
	(* [Rule 163] *)
	let
	    val I = case IntBasis.findSigId(IB, sigid)
		      of SOME I => I
		       | NONE   => errorSigId(I, "runtime error: unknown \
						 \signature ",sigid)
	in
	    I
	end

      | evalSigExp(IB, WHERETYPESigExp(I, sigexp, _, _, _)) =
	(* Omitted [Section 7.1] *)
	evalSigExp(IB, sigexp)


    (* Signature Declarations *)

    and evalSigDec(IB, SigDec(I, sigbind)) =
	(* [Rule 164] *)
	let
	    val G = evalSigBind(IB, sigbind)
	in
	    G
	end


    (* Signature Bindings *)

    and evalSigBind(IB, SigBind(I, sigid, sigexp, sigbind_opt)) =
	(* [Rule 165] *)
	let
	    val I = evalSigExp(IB, sigexp)
	    val G = case sigbind_opt
		      of NONE         => SigIdMap.empty
		       | SOME sigbind => evalSigBind(IB, sigbind)
	in
	    SigIdMap.insert(G, sigid, I)
	end


    (* Specifications *)

    and evalSpec(IB, VALSpec(I, valdesc)) =
	(* [Rule 166] *)
	let
	    val VI = evalValDesc(valdesc)
	in
	    Inter.fromVI VI
	end

      | evalSpec(IB, TYPESpec(I, typdesc)) =
	(* [Rule 167] *)
	let
	    val TI = evalTypDesc(typdesc)
	in
	    Inter.fromTI TI
	end

      | evalSpec(IB, EQTYPESpec(I, typdesc)) =
	(* [Rule 168] *)
	let
	    val TI = evalTypDesc(typdesc)
	in
	    Inter.fromTI TI
	end

      | evalSpec(IB, DATATYPESpec(I, datdesc)) =
	(* [Rule 169] *)
	let
	    val (VI,TI) = evalDatDesc(datdesc)
	in
	    Inter.fromVIandTI(VI,TI)
	end

      | evalSpec(IB, DATATYPE2Spec(I, tycon, longtycon)) =
	(* [Rule 170] *)
	let
	    val VI = case IntBasis.findLongTyCon(IB, longtycon)
		       of SOME VI => VI
			| NONE => errorLongTyCon(I, "runtime error: \
						    \unknown type ", longtycon)
	    val TI = TyConMap.singleton(tycon, VI)
	in
	    Inter.fromVIandTI(VI,TI)
	end

      | evalSpec(IB, EXCEPTIONSpec(I, exdesc)) =
	(* [Rule 171] *)
	let
	    val VI = evalExDesc(exdesc)
	in
	    Inter.fromVI VI
	end

      | evalSpec(IB, STRUCTURESpec(I, strdesc)) =
	(* [Rule 172] *)
	let
	    val SI = evalStrDesc(IB, strdesc)
	in
	    Inter.fromSI SI
	end

      | evalSpec(IB, INCLUDESpec(I, sigexp)) =
	(* [Rule 173] *)
	let
	    val I = evalSigExp(IB, sigexp)
	in
	    I
	end

      | evalSpec(IB, EMPTYSpec(I)) =
	(* [Rule 174] *)
	Inter.empty

      | evalSpec(IB, SEQSpec(I, spec1, spec2)) =
	(* [Rule 175] *)
	let
	    val I1 = evalSpec(IB, spec1)
	    val I2 = evalSpec(IntBasis.plusI(IB, I1), spec2)
	in
	    Inter.plus(I1,I2)
	end

      | evalSpec(IB, SHARINGTYPESpec(I, spec, longtycons)) =
	(* Omitted [Section 7.1] *)
	evalSpec(IB, spec)

      | evalSpec(IB, SHARINGSpec(I, spec, longstrids)) =
	(* Omitted [Section 7.1] *)
	evalSpec(IB, spec)


    (* Value Descriptions *)

    and evalValDesc(ValDesc(I, vid, _, valdesc_opt)) =
	(* [Rule 176] *)
	let
	    val VI = case valdesc_opt
		       of NONE         => VIdMap.empty
			| SOME valdesc => evalValDesc(valdesc)
	in
	    VIdMap.insert(VI, vid, IdStatus.v)
	end


    (* Type Descriptions *)

    and evalTypDesc(TypDesc(I, tyvarseq, tycon, typdesc_opt)) =
	(* [Rule 177] *)
	let
	    val TI = case typdesc_opt
		       of NONE         => TyConMap.empty
			| SOME typdesc => evalTypDesc(typdesc)
	in
	    TyConMap.insert(TI, tycon, VIdMap.empty)
	end


    (* Datatype Descriptions *)

    and evalDatDesc(DatDesc(I, tyvarseq, tycon, condesc, datdesc_opt)) =
	(* [Rule 178] *)
	let
	    val  VI       = evalConDesc(condesc)
	    val (VI',TI') = case datdesc_opt
			      of NONE          => ( VIdMap.empty, TyConMap.empty )
			       | SOME datdesc' => evalDatDesc(datdesc')
	in
	    ( VIdMap.unionWith #2 (VI, VI')
	    , TyConMap.insert(TI', tycon, VI)
	    )
	end


    (* Constructor Descriptions *)

    and evalConDesc(ConDesc(I, vid, _, condesc_opt)) =
	(* [Rule 179] *)
	let
	    val VI = case condesc_opt
		       of NONE         => VIdMap.empty
			| SOME condesc => evalConDesc(condesc)
	in
	    VIdMap.insert(VI, vid, IdStatus.c)
	end


    (* Exception Description *)

    and evalExDesc(ExDesc(I, vid, _, exdesc_opt)) =
	(* [Rule 180] *)
	let
	    val VI = case exdesc_opt
		       of NONE        => VIdMap.empty
			| SOME exdesc => evalExDesc(exdesc)
	in
	    VIdMap.insert(VI, vid, IdStatus.e)
	end


    (* Structure Descriptions *)

    and evalStrDesc(IB, StrDesc(I, strid, sigexp, strdesc_opt)) =
	(* [Rule 181] *)
	let
	    val I  = evalSigExp(IB, sigexp)
	    val SI = case strdesc_opt
		       of NONE         => StrIdMap.empty
		        | SOME strdesc => evalStrDesc(IB, strdesc)
	in
	    StrIdMap.insert(SI, strid, I)
	end


    (* Functor Bindings *)

    and evalFunBind(B, FunBind(I, funid, strid, sigexp, strexp, funbind_opt)) =
	(* [Rule 182] *)
	(* Note that there is a typo in this rule. *)
	let
	    val I  = evalSigExp(IntBasis.Inter B, sigexp)
	    val F  = case funbind_opt
		       of NONE         => FunIdMap.empty
			| SOME funbind => evalFunBind(B, funbind)
	in
	    FunIdMap.insert(F, funid, FunctorClosure((strid,I),strexp,B))
	end


    (* Functor Declarations *)

    and evalFunDec(B, FunDec(I, funbind)) =
	(* [Rule 183] *)
	let
	    val F = evalFunBind(B, funbind)
	in
	    F
	end


    (* Top-level Declarations *)

    and evalTopDec(s,B, STRDECTopDec(I, strdec, topdec_opt)) =
	(* [Rule 184] *)
	(* Note the mistake in the conclusion of this rule. *)
	let
	    val E   = evalStrDec(s,B, strdec)
	    val B'  = DynamicBasis.fromE E
	    val B'' = case topdec_opt
			of NONE        => DynamicBasis.empty
			 | SOME topdec => evalTopDec(s,B plus B', topdec)
	in
	    B' plus B''
	end

      | evalTopDec(s,B, SIGDECTopDec(I, sigdec, topdec_opt)) =
	(* [Rule 185] *)
	(* Note the mistake in the conclusion of this rule. *)
	let
	    val G   = evalSigDec(IntBasis.Inter B, sigdec)
	    val B'  = DynamicBasis.fromG G
	    val B'' = case topdec_opt
			of NONE        => DynamicBasis.empty
			 | SOME topdec => evalTopDec(s,B plus B', topdec)
	in
	    B' plus B''
	end

      | evalTopDec(s,B, FUNDECTopDec(I, fundec, topdec_opt)) =
	(* [Rule 186] *)
	(* Note the mistake in the conclusion of this rule. *)
	let
	    val F   = evalFunDec(B, fundec)
	    val B'  = DynamicBasis.fromF F
	    val B'' = case topdec_opt
			of NONE        => DynamicBasis.empty
			 | SOME topdec => evalTopDec(s,B plus B', topdec)
	in
	    B' plus B''
	end
end;
