module CTLlibrary

export *

signature:
	/*-----------CTL formulas------------*/
	static eg: Boolean -> Boolean	//exists globally
	static ex: Boolean -> Boolean	//exists next state
	static ef: Boolean -> Boolean	//exists finally
	static ag: Boolean -> Boolean	//forall globally
	static ax: Boolean -> Boolean	//forall next state
	static af: Boolean -> Boolean	//forall finally
	static e: Prod(Boolean, Boolean) -> Boolean	//exists until
	static a: Prod(Boolean, Boolean) -> Boolean //forall until

	/*-----------Patterns------------*/
	static ew: Prod(Boolean, Boolean) -> Boolean  //exists weak until -- E[p U q] | EGp.
	static aw: Prod(Boolean, Boolean) -> Boolean //forall weak until -- !E[!q U !(p | q)].


	//http://patterns.projects.cis.ksu.edu/documentation/patterns/ctl.shtml
	//Absence (P is false)
	//Globally - AG(!P)
	static absenceG: Boolean -> Boolean
	//(*) Before R - A[(!P | AG(!R)) W R]
	static absenceBefore: Prod(Boolean, Boolean) -> Boolean // absenceBefore(P, R)
	//After Q - AG(Q -> AG(!P))
	static absenceAfter: Prod(Boolean, Boolean) -> Boolean // absenceAfter(P, Q)
	//(*) Between Q and R - AG(Q & !R -> A[(!P | AG(!R)) W R])
	static absenceBetween: Prod(Boolean, Boolean, Boolean) -> Boolean // absenceBetween(P, Q, R)
	//(*) After Q until R - AG(Q & !R -> A[!P W R])
	static absenceAfterUntil: Prod(Boolean, Boolean, Boolean) -> Boolean // absenceAfterUntil(P, Q, R)

	//Precedence (S precedes P)
	//(*) Globally 	
	//A[!P W S]
	static ap: Prod(Boolean, Boolean) -> Boolean // ap(P, S)
	//(*) Before R 	
	//A[(!P | AG(!R)) W (S | R)]
	static pb: Prod(Boolean, Boolean, Boolean) -> Boolean // pb(P, S, R)
	//(*) After Q 	
	//A[!Q W (Q & A[!P W S])]
	//(*) Between Q and R 	
	//AG(Q & !R -> A[(!P | AG(!R)) W (S | R)])
	//(*) After Q until R 	
	//AG(Q & !R -> A[!P W (S | R)])

	//Response (S responds to P)
	//Globally
	//AG(P -> AF(S))
	//(*) Before R	
	//A[((P -> A[!R U (S & !R)]) | AG(!R)) W R]
	//(*) After Q	
	//A[!Q W (Q & AG(P -> AF(S))] 
	//(*) Between Q and R	
	//AG(Q & !R -> A[((P -> A[!R U (S & !R)]) | AG(!R)) W R])
	//(*) After Q until R	
	//AG(Q & !R -> A[(P -> A[!R U (S & !R)]) W R])

	/*-----------My CTL formulas------------*/
	static exN: Prod(Boolean, Natural) -> Boolean	//exists after N states
	static axN: Prod(Boolean, Natural) -> Boolean	//forall paths, after N states
definitions:
