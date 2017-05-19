module LTLlibrary

export *

signature:
	/*-----------LTL formulas------------*/ 
	//Future
	static x: Boolean -> Boolean			//next state
	static g: Boolean -> Boolean			//globally
	static f: Boolean -> Boolean			//finally
	static u: Prod(Boolean, Boolean) -> Boolean	//until
	static v: Prod(Boolean, Boolean) -> Boolean	//releases
	//Past
	static y: Boolean -> Boolean			//previous state
	static z: Boolean -> Boolean			//not previous state not
	static h: Boolean -> Boolean			//historically
	static o: Boolean -> Boolean			//once
	static s: Prod(Boolean, Boolean) -> Boolean	//since
	static t: Prod(Boolean, Boolean) -> Boolean	//triggered

definitions: