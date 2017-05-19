asm LandingGear

import ../../STDL/StandardLibrary
import ../../STDL/CTLlibrary
import ../../STDL/LTLlibrary

signature:
	enum domain HandleStatus = {UP | DOWN}
	enum domain DoorStatus = {CLOSED | OPENING | OPEN | CLOSING}
	enum domain GearStatus = {RETRACTED | EXTENDING | EXTENDED | RETRACTING}
	dynamic monitored handle: HandleStatus
	dynamic controlled doors: DoorStatus
	dynamic controlled gears: GearStatus

definitions:
	rule r_closeDoor =
		switch doors /*@extendable#doors*/
			case OPEN:
				doors := CLOSING
			case CLOSING:
				doors := CLOSED
			case OPENING:
				doors := CLOSING
		endswitch
							
						
		
rule r_retractionSequenceGears = 
		
					/*@extend_original#gearsR*/ switch gears /*@extendable#gearsR*/
						case EXTENDED:
							gears := RETRACTING
						case RETRACTING:
							gears := RETRACTED
						case EXTENDING:
							gears := RETRACTING
					endswitch
					
	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doors /*@extendable#doors*/
				case CLOSED:
					doors := OPENING
				case CLOSING:
					doors := OPENING
				case OPENING:
					doors := OPEN
				case OPEN:
					par
					r_retractionSequenceGears[]
					doors := OPEN
					endpar
			endswitch
		else
			r_closeDoor[]
		endif
			
rule r_outgoingSequenceGears =
		switch gears /*@extendable#gearso*/
						case RETRACTED:
							gears := EXTENDING
						case EXTENDING:
							gears := EXTENDED
						case RETRACTING:
							gears := EXTENDING
					endswitch

	rule r_outgoingSequence =
		if gears != EXTENDED then
			switch doors /*@extendable#doors*/
				case CLOSED:
					doors := OPENING
				case OPENING:
					doors := OPEN
				case CLOSING:
					doors := OPENING
				case OPEN:
					par
					r_outgoingSequenceGears[]
					doors := OPEN
					endpar
			endswitch 	
		else
			r_closeDoor[]
		endif

					
				
CTLSPEC ag((doors = CLOSED and gears = EXTENDED and ag(handle = DOWN)) implies ag(doors = CLOSED and gears = EXTENDED))
	CTLSPEC ag((doors = CLOSED and gears = RETRACTED and ag(handle = UP)) implies ag(doors = CLOSED and gears = RETRACTED))
	CTLSPEC ag((gears = EXTENDING and handle = DOWN) implies ax(gears = EXTENDED))
	CTLSPEC ag((gears = EXTENDING and handle = UP) implies ax(gears = RETRACTING))
	CTLSPEC ag((gears = RETRACTING and handle = UP) implies ax(gears = RETRACTED))
	CTLSPEC ag((gears = RETRACTING and handle = DOWN) implies ax(gears = EXTENDING))

	CTLSPEC ag((gears = EXTENDED and doors = CLOSING and handle = DOWN) implies ax(doors = CLOSED))
	CTLSPEC ag((gears = EXTENDED and doors = CLOSING and handle = UP) implies ax(doors = OPENING))
	CTLSPEC ag((gears = RETRACTED and doors = OPENING and handle = DOWN) implies ax(doors = OPEN))
	CTLSPEC ag((gears = RETRACTED and doors = OPENING and handle = UP) implies ax(doors = CLOSING))
	
	//R11_bis
	//CTLSPEC ag(ag(handle = DOWN) implies af(gears = EXTENDED and doors = CLOSED)) //WRONG
	//CTLSPEC ag(eg(handle = DOWN) implies ef(gears = EXTENDED and doors = CLOSED)) //TOO WEAK
	LTLSPEC g(g(handle = DOWN) implies f(gears = EXTENDED and doors = CLOSED))
	//R12_bis
	//CTLSPEC ag(ag(handle = UP) implies af(gears = RETRACTED and doors = CLOSED)) //WRONG
	//CTLSPEC ag(eg(handle = UP) implies ef(gears = RETRACTED and doors = CLOSED)) //TOO WEAK
	LTLSPEC g(g(handle = UP) implies f(gears = RETRACTED and doors = CLOSED))
	//R21
	//CTLSPEC ag(ag(handle = DOWN) implies ax(ag(gears != RETRACTING))) //WRONG
	//CTLSPEC ag(eg(handle = DOWN) implies ex(eg(gears != RETRACTING))) //TOO WEAK
	LTLSPEC g(g(handle = DOWN) implies x(g(gears != RETRACTING)))
	//R22
	//CTLSPEC ag(ag(handle = UP) implies ax(ag(gears != EXTENDING))) //WRONG
	//CTLSPEC ag(eg(handle = UP) implies ex(eg(gears != EXTENDING))) //TOO WEAK
	LTLSPEC g(g(handle = UP) implies x(g(gears != EXTENDING)))

	//Deadlock freeness
	CTLSPEC ag(ef(handle = UP)) //the handle can always become UP
	CTLSPEC ag(ef(handle = DOWN)) //the handle can always become DOWN
	//LTLSPEC (forall $s in DoorStatus with g(f(doors = $s))) //this fails
	//LTLSPEC (forall $s in GearStatus with g(f(gears = $s))) //this fails
	CTLSPEC (forall $s in DoorStatus with ag(ef(doors = $s)))
	CTLSPEC (forall $s in GearStatus with ag(ef(gears = $s)))

	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif

default init s0:
	function doors = CLOSED
	function gears = EXTENDED