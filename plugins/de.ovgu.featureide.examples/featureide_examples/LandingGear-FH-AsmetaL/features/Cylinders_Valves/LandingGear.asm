asm LandingGear



signature:
	enum domain CylinderStatus = {CYLINDER_RETRACTED | CYLINDER_EXTENDING | CYLINDER_EXTENDED | CYLINDER_RETRACTING}

	derived cylindersDoors: CylinderStatus
	derived cylindersGears: CylinderStatus

	dynamic controlled generalElectroValve: Boolean
	dynamic controlled openDoorsElectroValve: Boolean
	dynamic controlled closeDoorsElectroValve: Boolean
	dynamic controlled retractGearsElectroValve: Boolean
	dynamic controlled extendGearsElectroValve: Boolean


definitions:
	function cylindersDoors =
		switch doors
			case OPEN:
				CYLINDER_EXTENDED
			case OPENING:
				CYLINDER_EXTENDING
			case CLOSING:
				CYLINDER_RETRACTING
			case CLOSED:
				CYLINDER_RETRACTED
		endswitch

	function cylindersGears =
		switch gears
			case RETRACTED:
				CYLINDER_RETRACTED
			case EXTENDING:
				CYLINDER_EXTENDING
			case EXTENDED:
				CYLINDER_EXTENDED
			case RETRACTING:
				CYLINDER_RETRACTING
		endswitch

rule r_closeDoor =
	/*@extend_original#doors*/ switch doors /*@extendable#doors*/

			case OPEN:
				par
					closeDoorsElectroValve := true
					@original#doors
				endpar
			case CLOSING:
				par

					generalElectroValve := false
					closeDoorsElectroValve := false
					@original#doors
				endpar
			case OPENING:
				par
					closeDoorsElectroValve := true
					openDoorsElectroValve := false
					@original#doors
				endpar
		endswitch
 

rule r_retractionSequence =
		if gears != RETRACTED then

			/*@extend_original#doors*/ switch doors /*@extendable#doors*/
				case CLOSED:
					par
						generalElectroValve := true
						openDoorsElectroValve := true
						@original#doors
					endpar
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						@original#doors
					endpar
				case OPENING:
					par
						openDoorsElectroValve := false
						@original#doors
					endpar
	
			endswitch
		else
			r_closeDoor[]
		endif

rule r_outgoingSequenceGears =

	/*@extend_original#gearso*/ switch gears /*@extendable#gearso*/
						case EXTENDED:
							par
								retractGearsElectroValve := true
								@original#gearso
							endpar
						case RETRACTING:
							par
								retractGearsElectroValve := false
								@original#gearso
							endpar
						case EXTENDING:
							par
								extendGearsElectroValve := false
								retractGearsElectroValve := true
								@original#gearso
							endpar
					endswitch


	rule r_outgoingSequence =
		if gears != EXTENDED then
			/*@extend_original#doors*/ switch doors /*@extendable#doors*/
				case CLOSED:
					par
						generalElectroValve := true
						openDoorsElectroValve := true
						@original#doors
					endpar
				case OPENING:
					par
						openDoorsElectroValve := false
						@original#doors
					endpar
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						@original#doors
					endpar

			endswitch
		else
			r_closeDoor[]
		endif

	CTLSPEC ag(generalElectroValve implies ef(not(generalElectroValve)))
	//R31
	CTLSPEC ag((extendGearsElectroValve or retractGearsElectroValve) implies doors = OPEN)
	LTLSPEC g((extendGearsElectroValve or retractGearsElectroValve) implies doors = OPEN)
	//R32
	CTLSPEC ag((openDoorsElectroValve or closeDoorsElectroValve) implies (gears = RETRACTED or gears = EXTENDED))
	LTLSPEC g((openDoorsElectroValve or closeDoorsElectroValve) implies (gears = RETRACTED or gears = EXTENDED))
	//R41
	CTLSPEC ag(not(openDoorsElectroValve and closeDoorsElectroValve))
	LTLSPEC g(not(openDoorsElectroValve and closeDoorsElectroValve))
	//R42
	CTLSPEC ag(not(extendGearsElectroValve and retractGearsElectroValve))
	LTLSPEC g(not(extendGearsElectroValve and retractGearsElectroValve))
	//R51
	CTLSPEC ag((openDoorsElectroValve or closeDoorsElectroValve or extendGearsElectroValve or retractGearsElectroValve) implies generalElectroValve)
	LTLSPEC g((openDoorsElectroValve or closeDoorsElectroValve or extendGearsElectroValve or retractGearsElectroValve) implies generalElectroValve)
	
	

default init s0:
		@original()
		function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false