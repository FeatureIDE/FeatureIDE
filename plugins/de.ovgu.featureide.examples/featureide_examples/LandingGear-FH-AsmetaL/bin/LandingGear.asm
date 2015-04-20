asm  LandingGear


import ../../StandardLibrary 

signature: 
	enum domain HandleStatus = {UP | DOWN} 
	enum domain DoorStatus = {CLOSED | OPENING | OPEN | CLOSING} 
	enum domain GearStatus = {RETRACTED | EXTENDING | EXTENDED | RETRACTING} 
	enum domain CylinderStatus = {CYLINDER_RETRACTED | CYLINDER_EXTENDING | CYLINDER_EXTENDED | CYLINDER_RETRACTING} 
	dynamic monitored handle: HandleStatus 
	dynamic controlled doors: DoorStatus 
	dynamic controlled gears: GearStatus 
	derived doorsv2: DoorStatus 
	derived gearsv2: GearStatus 

	dynamic controlled cylindersDoors: CylinderStatus 
	dynamic controlled cylindersGears: CylinderStatus 
	dynamic controlled generalElectroValve: Boolean 
	dynamic controlled openDoorsElectroValve: Boolean 
	dynamic controlled closeDoorsElectroValve: Boolean 
	dynamic controlled retractGearsElectroValve: Boolean 
	dynamic controlled extendGearsElectroValve: Boolean 

	dynamic monitored gearsExtended: Boolean 
	dynamic monitored gearsRetracted: Boolean 
	dynamic monitored doorsClosed: Boolean 
	dynamic monitored doorsOpen: Boolean 
	dynamic monitored gearsShockAbsorber: Boolean



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
		switch doorsv2
			case OPEN:
				par
					closeDoorsElectroValve := true
					cylindersDoors := CYLINDER_RETRACTING
				endpar
			case OPENING:
				par
					closeDoorsElectroValve := true
					openDoorsElectroValve := false
					cylindersDoors := CYLINDER_RETRACTING
				endpar
		case CLOSING: 
				if doorsClosed then
					
				par
					generalElectroValve := false //quando si chiude la porta vuol dire che una manovra è terminata. quindi si può spegnere la valvola generale
					closeDoorsElectroValve := false
					cylindersDoors := CYLINDER_RETRACTED
				endpar
			
				endif
		
endswitch 

	rule r_retractionSequence =
		if gears != RETRACTED then
			switch doorsv2
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote estese (e si riceve il segnale UP)
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case OPEN: 
					switch gearsv2
						case RETRACTING: 
							if gearsRetracted then
								
							par
								retractGearsElectroValve := false
								cylindersGears := CYLINDER_RETRACTED
							endpar
						
							endif
					case EXTENDED: 
							if gearsShockAbsorber then
								
							par
								retractGearsElectroValve := true
								cylindersGears := CYLINDER_RETRACTING
							endpar
						
							endif
						case EXTENDING:
							par
								extendGearsElectroValve := false
								retractGearsElectroValve := true
								cylindersGears := CYLINDER_RETRACTING
							endpar
					
endswitch
			case OPENING: 
					if doorsOpen then
						
					par
						openDoorsElectroValve := false
						cylindersDoors := CYLINDER_EXTENDED
					endpar
				
					endif
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				
endswitch
		else
			r_closeDoor[]
		endif 

	rule r_outgoingSequence =
		if gears != EXTENDED then
			switch doorsv2
				case CLOSED:
					par
						generalElectroValve := true //si apre la valvola generale quando la porta è chiusa con le ruote retratte (e si riceve il segnale DOWN)
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				case OPEN: 
					switch gearsv2
						case RETRACTED:
							par
								extendGearsElectroValve := true
								cylindersGears := CYLINDER_EXTENDING
							endpar
						case RETRACTING:
							par
								extendGearsElectroValve := true
								retractGearsElectroValve := false
								cylindersGears := CYLINDER_EXTENDING
							endpar
					case EXTENDING: /*@compose@gears*/
							if gearsExtended then
								
							par
								extendGearsElectroValve := false
								cylindersGears := CYLINDER_EXTENDED
							endpar
						
							endif
					
endswitch
			case OPENING: 
					if doorsOpen then
						
					par
						openDoorsElectroValve := false
						cylindersDoors := CYLINDER_EXTENDED
					endpar
				
					endif
				case CLOSING:
					par
						closeDoorsElectroValve := false
						openDoorsElectroValve := true
						cylindersDoors := CYLINDER_EXTENDING
					endpar
				
endswitch
		else
			r_closeDoor[]
		endif 

	invariant over gearsv2, doorsv2: (gearsv2 = EXTENDING or gearsv2 = RETRACTING) implies doorsv2 = OPEN 

	invariant over gearsv2, doorsv2: (gearsv2 = EXTENDING or gearsv2 = RETRACTING) implies doorsv2 = OPEN


	main rule r_Main =
		if handle = UP then
			r_retractionSequence[]
		else
			r_outgoingSequence[]
		endif


default  init s0:
	function cylindersDoors = CYLINDER_RETRACTED
	function cylindersGears = CYLINDER_EXTENDED
	function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false
