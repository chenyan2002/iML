(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML implementation main structure
 *)

structure Sml : SML =
struct
    (* Initial arguments *)

    (*type arg = (Infix.InfEnv * BindingBasis.Basis) * Basis.Basis * Program.State*)
    type arg = (Infix.InfEnv * BindingBasis.Basis) * Basis.Basis * EvalModule.State
    
    val J0          = InitialInfixEnv.J0

    val B0_BIND     = StaticBasis.toBindingBasis InitialStaticBasis.B0
    val B0_BIND'    = StaticBasis.toBindingBasis Library.B0_STAT
    val B0_STAT     = InitialStaticBasis.B0
    val B0_DYN      = InitialDynamicBasis.B0
    val B0          = (B0_STAT, B0_DYN)
    val B0'         = (Library.B0_STAT, Library.B0_DYN)
    val s0          = InitialDynamicBasis.s0
    val s0'         = Library.s0
(*
    val initialArg  = ((J0,B0_BIND), B0, s0)
    val initialArg' = ((J0,B0_BIND'), B0', s0')
*)
    val initialArg  = ((J0,B0_BIND), B0, s0)
    val initialArg' = ((J0,B0_BIND'), B0', s0')

    (* Parsing only *)

    val checkProgram = SyntacticRestrictionsProgram.checkProgram

    fun parseArg (JB,B,s) = JB

    fun parse (J, B_BIND) (filenameOpt, source) =
	let
	    val (J',program) = Parse.parse(J, source, filenameOpt)
	    val (B_BIND',program)     = checkProgram(B_BIND, program)
	    val  _           = PPProgram.ppProgram(TextIO.stdOut, 0, program)
	in
	    (J', B_BIND')
	end

    (* Parsing and elaboration *)

    fun printStaticBasis B_STAT =
	( PrettyPrint.output(TextIO.stdOut, PPStaticBasis.ppBasis B_STAT,
			     79)
	; TextIO.flushOut TextIO.stdOut
	)

    fun execProgram echo (s,B, GrammarProgram.Program(I, topdec, program_opt)) =
	(* [Rules 187 to 189] *)
	let
            val oplus = Basis.oplus
            infix oplus
	    val B_STAT1 = ElabModule.elabTopDec(Basis.B_STATof B, topdec)
	    val B_DYN1  = EvalModule.evalTopDec(s,Basis.B_DYNof B, topdec)
	    (* [Rule 189] *)
	    (*val _       = if echo then printBasis(!s, (B_STAT1,B_DYN1)) else ()*)
	    val B'      = B oplus (B_STAT1,B_DYN1)
	    val B''     = case program_opt
			    of NONE         => B'
			     | SOME program => execProgram echo (s,B', program)
	in
	    B''
	end
	handle Error.Error =>
	       (* [Rule 187] *)
	       let
		   val B' = case program_opt
			      of NONE         => B
			       | SOME program => execProgram echo (s,B, program)
	       in
		   B'
	       end

	     | DynamicObjectsCore.Pack e =>
	       (* [Rule 188] *)
	       let
		   (*val _  = printException(!s, e)*)
		   val B' = case program_opt
			      of NONE         => B
			       | SOME program => execProgram echo (s,B, program)
	       in
		   B'
	       end


    fun elabProgram echo (B_STAT, GrammarProgram.Program(I, topdec, program_opt)) =
	let
	    val B_STAT1  = ElabModule.elabTopDec(B_STAT, topdec)
	    val  _       = if echo then printStaticBasis B_STAT1 else ()
	    val B_STAT'  = StaticBasis.plus(B_STAT, B_STAT1)
	    val B_STAT'' = case program_opt
			     of NONE         => B_STAT'
			      | SOME program =>
				   elabProgram echo (B_STAT', program)
	in
	    B_STAT''
	end
	handle Error.Error =>
	       B_STAT

    fun elabArg ((J,B_BIND), (B_STAT,B_DYN),s) = (J, B_BIND, B_STAT)

    fun elab (J, B_BIND, B_STAT) (filenameOpt, source) =
	let
	    val (J',program) = Parse.parse(J, source, filenameOpt)
	    val  (B_BIND',program)     = checkProgram(B_BIND, program)
	    val  B_STAT'     = elabProgram true (B_STAT, program)
            (*val  _           = PPProgram.ppProgram(TextIO.stdOut, 0, program)*)
            val  _           = SMLProgram.printSML (B_STAT', program)
	in
	    (J', B_BIND', B_STAT')
	end

(*
    (* Parsing and evaluation *)

    fun evalArg ((J,B_BIND), (B_STAT,B_DYN), s) = (J, B_BIND, B_DYN, s)

    fun eval (J, B_BIND, B_DYN, s) (filenameOpt, source) =
	let
	    val (J',program) = Parse.parse(J, source, filenameOpt)
	    val  B_BIND'     = checkProgram(B_BIND, program)
	    val  s'          = ref s
	    val  B_DYN'      = Program.evalProgram true (s', B_DYN, program)
	in
	    (J', B_BIND', B_DYN', !s')
	end
*)

    (* Parsing, elaboration, and evaluation *)

    fun execArg arg = arg

    fun exec' echo ((J,B_BIND), B,s) (filenameOpt, source) =
	let
	    val (J',program) = Parse.parse(J, source, filenameOpt)
	    val  (B_BIND',program)     = checkProgram(B_BIND, program)
            val  s' = ref s
	    val  B'          = execProgram echo (s', B, program)
	in
	    ((J',B_BIND'), B', !s')
	end

    val exec = exec' true


    (* Process the `use' queue *)

    fun uses fromFile (process, arg) =
	case Use.extract()
	  of NONE      => arg
	   | SOME name => uses fromFile (process, fromFile (process, arg) name)


    (* Processing of strings *)

    fun fromString'' fromUsedFile (process, arg) (filenameOpt, source) =
	let
	    val arg' = process arg (filenameOpt, source)
		       handle Error.Error => arg	(* Syntax error *)
	in
	    uses fromUsedFile (process, arg')
	end

    fun fromString' fromUsedFile (process, arg) source =
	fromString'' fromUsedFile (process, arg) (NONE, source)

    fun fromInput' fromUsedFile (process, arg) (n, source) =
	fromString'' fromUsedFile (process, arg)
		     (SOME("(input "^Int.toString n^")"), source)


    (* Processing of files *)

    fun fromFile' fromUsedFile (process, arg) name =
	let
	    val file   = TextIO.openIn name
	    val source = TextIO.inputAll file ^ ";"
	    val _      = TextIO.closeIn file
	    val dir    = OS.FileSys.getDir()
	    val dir'   = case OS.Path.dir name of ""   => OS.Path.currentArc
						| dir' => dir'
	in
	    OS.FileSys.chDir dir';
	    fromString'' fromUsedFile (process, arg) (SOME name, source)
	    before OS.FileSys.chDir dir
	end
	handle IO.Io _ =>
	    ( TextIO.output(TextIO.stdErr, name ^ ": read error\n") ; arg )

    fun fromFileLogged (process, arg) name =
	( TextIO.output(TextIO.stdOut, "[processing " ^ name ^ "]\n")
	; TextIO.flushOut TextIO.stdOut
	; fromFile' fromFileLogged (process, arg) name
	)

    fun fromString args    = fromString' fromFileLogged args
    fun fromInput args     = fromInput' fromFileLogged args
    fun fromFile args      = fromFile' fromFileLogged args
    fun fromFileQuiet args = fromFile' fromFileQuiet args


    (* Processing several files mentioned in a list file *)

    fun fromFiles (process, initialArg) names =
	List.foldl (fn (name, arg) =>
		    fromFileLogged (process, initialArg) name) initialArg names


    (* Session *)

    fun fromSession (process, initialArg) =
	let
	    fun inputLines prompt =
		let
		    val _    = TextIO.output(TextIO.stdOut, prompt)
		    val _    = TextIO.flushOut TextIO.stdOut
		    val line = TextIO.inputLine TextIO.stdIn
		in
		    case line
		      of NONE      => nil
		       | SOME "\n" => "\n" :: inputLines "  "
		       | SOME text =>
			 if String.sub(text, String.size text - 2) = #";" then
			     text :: nil
			 else
			     text :: inputLines "  "
		end

	    fun loop(n, arg) =
		case inputLines "- "
		  of nil   => ()
		   | lines => loop(n+1, fromInput (process, arg)
						  (n, String.concat lines))
	in
	    loop(1, initialArg)
	end


    (* Install library *)

    val basisPath = ref "basis"

    fun loadLib() =
	( TextIO.output(TextIO.stdOut, "[loading standard basis library]\n")
	; TextIO.flushOut TextIO.stdOut
	; fromFileQuiet (exec' false, initialArg')
			(OS.Path.joinDirFile{dir  = !basisPath,
					     file = Library.file})
	)
	handle IO.Io _ =>
	( TextIO.output(TextIO.stdOut, "[library not found]\n")
	; initialArg
	)

    val libRef = ref(NONE : arg option)

    fun lib() =	case !libRef of SOME arg => arg
			      | NONE => ( libRef := SOME(loadLib()); lib() )


    (* Plumbing *)

    fun processString (f, arg) s   = ignore(fromString (f, arg(lib())) s)
    fun processFile   (f, arg) s   = ignore(fromFile (f, arg(lib())) s)
    fun processFiles  (f, arg) s   = ignore(fromFiles (f, arg(lib())) s)
    fun processSession (f, arg) () = fromSession(f, arg(lib()))

    val parseString  = processString(parse, parseArg)
    val elabString   = processString(elab, elabArg)
(*
    val evalString   = processString(eval, evalArg)
    val execString   = processString(exec, execArg)
*)
    val parseFile    = processFile(parse, parseArg)
    val elabFile     = processFile(elab, elabArg)
(*
    val evalFile     = processFile(eval, evalArg)
    val execFile     = processFile(exec, execArg)
*)
    val parseFiles   = processFiles(parse, parseArg)
    val elabFiles    = processFiles(elab,  elabArg)
(*
    val evalFiles    = processFiles(eval,  evalArg)
    val execFiles    = processFiles(exec,  execArg)
*)
    val parseSession = processSession(parse, parseArg)
    val elabSession  = processSession(elab,  elabArg)
(*
    val evalSession  = processSession(eval,  evalArg)
    val execSession  = processSession(exec,  execArg)
*)
end;
