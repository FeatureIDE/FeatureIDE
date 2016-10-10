asm LandingGear

import ../../StandardLibrary

signature:
	enum domain CylinderStatus = {CYLINDER_RETRACTED | CYLINDER_EXTENDING | CYLINDER_EXTENDED | CYLINDER_RETRACTING}
	dynamic monitored handle: HandleStatus
	derived doorsv2: DoorStatus
	derived gearsv2: GearStatus

	dynamic controlled cylindersDoors: CylinderStatus
	dynamic controlled cylindersGears: CylinderStatus
	dynamic controlled generalElectroValve: Boolean
	dynamic controlled openDoorsElectroValve: Boolean
	dynamic controlled closeDoorsElectroValve: Boolean
	dynamic controlled retractGearsElectroValve: Boolean
	dynamic controlled extendGearsElectroValve: Boolean

definitions:
	function doorsv2 =
		switch cylindersDoors
			case CYLINDER_EXTENDED:
				OPEN
			case CYLINDER_EXTENDING:
				OPENING
			case CYLINDER_RETRACTING:
				CLOSING
			case CYLINDER_RETRACTED:
				CLOSED
		endswitch

	function gearsv2 =
		switch cylindersGears
			case CYLINDER_RETRACTED:
				RETRACTED
			case CYLINDER_EXTENDING:
				EXTENDING
			case CYLINDER_EXTENDED:
				EXTENDED
			case CYLINDER_RETRACTING:
				RETRACTING
		endswitch

	rule r_closeDoor =
		switch doorsv2 /*@extendable#doors*/
			case OPEN:
				par
					closeDoorsElectroValve := true
					cylindersDoors := CYLINDER_RETRACTING
				endpar
			case CLOSING:
				par
					generalElectroValve := false //quando si chiude la porta vuol dire che una manovra è terminata. quindi si può spegnere la valvola generale
					closeDoorsElectroValve := false
					cylindersDoors := CYLINDER_RETRACTED
				endpar
			case OPENING:
				par
					closeDoorsElectroValve := true
					openDoorsElectroValve := false
					cylindersDoors := CYLINDER_RETRACTING
				endpar
		endswitch

	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doorsv2 /*@extendable#doors*/
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote estese (e si riceve il segnale UP)
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case OPENING:
					par
						openDoorsElectroValve := false
						cylindersDoors := CYLINDER_EXTENDED
					endpar
				case OPEN:
					switch gearsv2 /*@extendable#gears*/
						case EXTENDED:
							par
								retractGearsElectroValve := true
								cylindersGears := CYLINDER_RETRACTING
							endpar
						case RETRACTING:
							par
								retractGearsElectroValve := false
								cylindersGears := CYLINDER_RETRACTED
							endpar
						case EXTENDING:
							par
								extendGearsElectroValve := false
								retractGearsElectroValve := true
								cylindersGears := CYLINDER_RETRACTING
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	rule r_outgoingSequence =
		if gears != EXTENDED then
			switch doorsv2 /*@extendable#doors*/
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote retratte (e si riceve il segnale DOWN)
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case OPENING:
					par
						openDoorsElectroValve := false
						cylindersDoors := CYLINDER_EXTENDED
					endpar
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case OPEN:
					switch gearsv2 /*@extendable#gears*/
						case RETRACTED:
							par
								extendGearsElectroValve := true
								cylindersGears := CYLINDER_EXTENDING
							endpar
						case EXTENDING:
							par
								extendGearsElectroValve := false
								cylindersGears := CYLINDER_EXTENDED
							endpar
						case RETRACTING:
							par
								extendGearsElectroValve := true
								retractGearsElectroValve := false
								cylindersGears := CYLINDER_EXTENDING
							endpar
					endswitch
			endswitch
		else
			r_closeDoor[]
		endif

	//sono anche tradotti in proprietà CTL
	invariant over gearsv2, doorsv2: (gearsv2 = EXTENDING or gearsv2 = RETRACTING) implies doorsv2 = OPEN
	invariant over gearsv2, doorsv2: doorsv2 = CLOSED implies (gearsv2 = EXTENDED or gearsv2 = RETRACTED)

	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif

default init s0:
	function cylindersDoors = CYLINDER_RETRACTED
	function cylindersGears = CYLINDER_EXTENDED
	function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false
