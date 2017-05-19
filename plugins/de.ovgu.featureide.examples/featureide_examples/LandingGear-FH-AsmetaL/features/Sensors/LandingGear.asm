asm LandingGear

signature:

	//sensors
	//gearsExtended is true if the corresponding gear is locked in the extended position and false in the other case
	dynamic monitored gearsExtended: Boolean
	//gearsRetracted is true if the corresponding gear is locked in the retracted position and false in the other case
	dynamic monitored gearsRetracted: Boolean
	//doorsClosed($s) is true if and only if the corresponding door is locked closed
	dynamic monitored doorsClosed: Boolean
	//doorsOpen is true if and only if the corresponding door is locked open
	dynamic monitored doorsOpen: Boolean
	//gearsShockAbsorber is true if and only if the aircfraft is on ground
	dynamic monitored gearsShockAbsorber: Boolean


definitions:

	rule r_closeDoor =
		/*@extend_original#doors*/ switch doors /*@extendable#doors*/
				case CLOSING: /*@compose#doors*/
					if doorsClosed then
						@original#doors
					endif
			endswitch

	rule r_retractionSequence =
		if gears != RETRACTED then
			/*@extend_original#doors*/ switch doors /*@extendable#doors*/
				case OPENING: /*@compose#doors*/

					if doorsOpen then
						@original#doors

					endif
			
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_retractionSequenceGears =
		/*@extend_original#gears*/ switch gears /*@extendable#gears*/
						case EXTENDED:
							if gearsShockAbsorber then
								@original#gears

							endif
						case RETRACTING:
							if gearsRetracted then
								@original#gears	

							endif
					endswitch
					
	rule r_outgoingSequence =
		if gears != EXTENDED then
			/*@extend_original#doors*/ switch doors /*@extendable#doors*/

				case OPENING:
					if doorsOpen then
						@original#doors

					endif
				
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequenceGears=

					/*@extend_original#gears*/switch gears /*@extendable#gears*/

						case EXTENDING:
							if gearsExtended then
								@original#gears

							endif

					endswitch
					
					
	//sensors must be true infinitely often (necessary for property verification)

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

	


