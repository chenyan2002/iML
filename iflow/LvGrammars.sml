(*
 * (c) Andreas Rossberg 1999-2007
 *
 * Standard ML grammar
 *)

structure LvCore    = LvCoreFn(type Info = Source.info)

structure LvModule  = LvModuleFn(type Info = Source.info
                                 structure Core = LvCore)

structure LvProgram = GrammarProgramFn(type Info = Source.info
				       structure Module = LvModule);
