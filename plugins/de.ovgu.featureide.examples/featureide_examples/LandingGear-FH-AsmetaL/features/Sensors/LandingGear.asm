asm LandingGear

signature:

definitions:

	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doors /*extendable#doors*/
				case OPENING: /*@compose#doors*/
					if doorsOpen then
						@original#doors
					endif
				case OPEN: /*@compose#doors*/
					/*@extend_original#gears*/ switch gears
						case EXTENDED:
							if gearsShockAbsorber then
								@original#gears
							endif
						case RETRACTING:
							if gearsRetracted then
								@original#gears
							endif
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequence =
		if gears != EXTENDED then
			/*@extend_original#doors*/ switch doors /*extendable#doors*/
				case OPENING:
					if doorsOpen then
						@original#doors
					endif
				case OPEN: /*@compose#doors*/
					switch gears /*@extendable#gears*/
						case EXTENDING:
							if gearsExtended then
								@original#gears
							endif
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

