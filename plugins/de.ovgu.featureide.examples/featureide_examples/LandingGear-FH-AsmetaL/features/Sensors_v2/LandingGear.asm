asm LandingGear

import ../../StandardLibrary

signature:

	dynamic monitored gearsExtended: Boolean
	dynamic monitored gearsRetracted: Boolean
	dynamic monitored doorsClosed: Boolean
	dynamic monitored doorsOpen: Boolean
	dynamic monitored gearsShockAbsorber: Boolean

definitions:
	rule r_closeDoor =
		/*@extend_original#doors*/ switch doorsv2
			case CLOSING: /*@compose#doors*/
				if doorsClosed then
					@original#doors
				endif
		endswitch

	rule r_retractionSequence =
		if gears != RETRACTED then
			/*@extend_original#doors*/ switch doorsv2
				case OPENING: /*@compose#doors*/
					if doorsOpen then
						@original#doors
					endif
				case OPEN: /*@compose#doors*/
					/*@extend_original#gears*/ switch gearsv2
						case EXTENDED: /*@compose#gears*/
							if gearsShockAbsorber then
								@original#gears
							endif
						case RETRACTING: /*@compose#gears*/
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
			/*@extend_original#doors*/ switch doorsv2
				case OPENING: /*@compose#doors*/
					if doorsOpen then
						@original#doors
					endif
				case OPEN: /*@compose#doors*/
					/*@extend_original#gears*/ switch gearsv2
						case EXTENDING: /*@compose@gears*/
							if gearsExtended then
								@original#gears
							endif
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	invariant over gearsv2, doorsv2: (gearsv2 = EXTENDING or gearsv2 = RETRACTING) implies doorsv2 = OPEN
	invariant over gearsv2, doorsv2: doorsv2 = CLOSED implies (gearsv2 = EXTENDED or gearsv2 = RETRACTED)

	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif
