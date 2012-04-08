(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML type names and sets and maps thereof
 *
 * Definition, Sections 4.1, 4.2, 5.1 and 5.2
 *
 * Notes:
 * - Equality is not a boolean attribute. We distinguish a 3rd kind of special
 *   type names which have equality regardless of the types applied. This
 *   implements ref, array, and equivalent types.
 * - For easy checking of pattern exhaustiveness we add an attribute
 *   `span' counting the number of constructors of the type.
 * - For checking of declaration orders etc we provide access to a time stamp.
 *)

structure TyName :> TYNAME =
struct
    (* Type [Section 4.1] *)

    type TyName =				      (* [t] *)
	 { tycon :	string
	 , stamp :	Stamp.stamp
	 , arity :	int
	 , equality :	bool
	 , span :	int
         , level :      Level.t
	 }


    (* Creation *)

    fun tyname(tycon, arity, equality, span, level) =
	{ tycon    = tycon
	, stamp    = Stamp.stamp()
	, arity    = arity
	, equality = equality
	, span     = span
        , level    = level
	}

    fun invent(arity, equality) =
	tyname("_id" ^ Stamp.toString(Stamp.stamp()), arity, equality, 0, Level.Unknown)


    (* Creation from existing *)

    fun rename {tycon, stamp, arity, equality, span, level} =
	    tyname(tycon, arity, equality, span, level)

    fun removeEquality {tycon, stamp, arity, equality, span, level} =
	    tyname(tycon, arity, false, span,level)

    fun Abs {tycon, stamp, arity, equality, span, level} =
	    tyname(tycon, arity, false, 0, level)


    (* Attributes [Section 4.1] *)

    fun arity{tycon, stamp, arity, equality, span, level} = arity
    fun time {tycon, stamp, arity, equality, span, level} = stamp
    fun span {tycon, stamp, arity, equality, span, level} = span
    fun toString{tycon, stamp, arity, equality, span, level} = tycon ^ (Level.toString level)
    fun admitsEquality{tycon, stamp, arity, equality, span, level} = equality
    fun level {tycon, stamp, arity, equality, span, level} = level


    (* Ordering *)

    fun compare(t1 : TyName, t2 : TyName) = Stamp.compare(#stamp t1, #stamp t2)
end

structure TyNameSet = FinSetFn(type ord_key = TyName.TyName
			       val  compare = TyName.compare)
structure TyNameMap = FinMapFn(type ord_key = TyName.TyName
			       val  compare = TyName.compare);
