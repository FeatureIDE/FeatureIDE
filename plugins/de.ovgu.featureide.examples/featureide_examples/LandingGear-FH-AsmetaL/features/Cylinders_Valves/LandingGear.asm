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

	derived gearsExtended: Boolean
	derived gearsRetracted: Boolean
	derived doorsClosed: Boolean
	derived doorsOpen: Boolean
	derived gearsShockAbsorber: Boolean

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
		/*@extend_original#doors*/ switch doors
			case OPEN:
				par
					closeDoorsElectroValve := true
					@original#doors
				endpar
			case CLOSING:
				par
					generalElectroValve := false //quando si chiude la porta vuol dire che una manovra è terminata. quindi si può spegnere la valvola generale
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
			/*@extend_original#doors*/ switch doors
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote estese (e si riceve il segnale UP)
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
				case OPEN:
					/*@extend_original#gears*/ switch gears
						case EXTENDED:
							par
								retractGearsElectroValve := true
								@original#gears
							endpar
						case RETRACTING:
							par
								retractGearsElectroValve := false
								@original#gears
							endpar
						case EXTENDING:
							par
								extendGearsElectroValve := false
								retractGearsElectroValve := true
								@original#gears
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequence =
		if gears != EXTENDED then
			/*@extend_original#doors*/ switch doors
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote retratte (e si riceve il segnale DOWN)
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
				case OPEN:
					/*@extend_original#gears*/ switch gears
						case RETRACTED:
							par
								extendGearsElectroValve := true
								@original#gears
							endpar
						case EXTENDING:
							par
								extendGearsElectroValve := false
								@original#gears
							endpar
						case RETRACTING:
							par
								extendGearsElectroValve := true
								retractGearsElectroValve := false
								@original#gears
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

default init s0:
	@original()
	function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false
