asm LandingGear

signature:

	dynamic controlled extendGearsElectroValve: Boolean


	derived aGearExtended: Boolean
	derived aGearRetracted: Boolean
	derived aDoorClosed: Boolean
	derived aDoorOpen: Boolean

	dynamic monitored timeout: Boolean
	dynamic controlled anomaly: Boolean

	derived greenLight: Boolean
	derived orangeLight: Boolean
	derived redLight: Boolean

definitions:


	function aGearExtended = (exist $s in LandingSet with gearsExtended($s))
	function aGearRetracted = (exist $s in LandingSet with gearsRetracted($s))
	function aDoorClosed = (exist $s in LandingSet with doorsClosed($s))
	function aDoorOpen = (exist $s in LandingSet with doorsOpen($s))
	function gearsShockAbsorber = (forall $s in LandingSet with gearsShockAbsorber($s))

	function greenLight = gears = EXTENDED
	function orangeLight = gears = EXTENDING or gears = RETRACTING
	function redLight = anomaly

	
	rule r_healthMonitoring =
		par
			if openDoorsElectroValve and aDoorClosed and timeout then
				anomaly := true
			endif
			if openDoorsElectroValve and not(doorsOpen) and timeout then
				anomaly := true
			endif
			if closeDoorsElectroValve and aDoorOpen and timeout then
				anomaly := true
			endif
			if closeDoorsElectroValve and not(doorsClosed) and timeout then
				anomaly := true
			endif

			if retractGearsElectroValve and aGearExtended and timeout then
				anomaly := true
			endif
			if retractGearsElectroValve and not(gearsRetracted) and timeout then
				anomaly := true
			endif
			if extendGearsElectroValve and aGearRetracted and timeout then
				anomaly := true
			endif
			if extendGearsElectroValve and not(gearsExtended) and timeout then
				anomaly := true
			endif
		endpar

	/*
	//sensors must be true infinitely often (necessary for property verification)
	JUSTICE timeout or gearsExtended
	JUSTICE timeout or gearsRetracted
	JUSTICE timeout or doorsClosed
	JUSTICE timeout or doorsOpen
	JUSTICE gearsShockAbsorber
	//JUSTICE timeout

	/*CTLSPEC ag((generalElectroValve and eg(not(anomaly))) implies ef(not(generalElectroValve) and not(anomaly)))

	//LTLSPEC g(g(handle = DOWN) implies f(gears = EXTENDED and doors = CLOSED)) //it fails because of the anomaly
	LTLSPEC g(g(handle = DOWN and not(anomaly)) implies f(gears = EXTENDED and doors = CLOSED))
	//LTLSPEC g(g(handle = UP) implies f(gears = RETRACTED and doors = CLOSED)) //it fails because of the anomaly
	LTLSPEC g(g(handle = UP and not(anomaly)) implies f(gears = RETRACTED and doors = CLOSED))
	//CTLSPEC ag(eg(handle = DOWN and not(anomaly)) implies ex(eg(gears != RETRACTING))) //TOO WEAK
	//LTLSPEC g(g(handle = DOWN) implies x(g(gears != RETRACTING))) //it fails because of the anomaly
	LTLSPEC g(g(handle = DOWN and not(anomaly)) implies x(g(gears != RETRACTING)))
	//CTLSPEC ag(eg(handle = UP and not(anomaly)) implies ex(eg(gears != EXTENDING))) //TOO WEAK
	//LTLSPEC g(g(handle = UP) implies x(g(gears != EXTENDING))) //it fails because of the anomaly
	LTLSPEC g(g(handle = UP and not(anomaly)) implies x(g(gears != EXTENDING)))

	//R61
	CTLSPEC ag((openDoorsElectroValve and aDoorClosed and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((openDoorsElectroValve and aDoorClosed and timeout) implies x(g(anomaly)))
	//R62
	CTLSPEC ag((closeDoorsElectroValve and aDoorOpen and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((closeDoorsElectroValve and aDoorOpen and timeout) implies x(g(anomaly)))
	//R63
	CTLSPEC ag((retractGearsElectroValve and aGearExtended and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((retractGearsElectroValve and aGearExtended and timeout) implies x(g(anomaly)))
	//R64
	CTLSPEC ag((extendGearsElectroValve and aGearRetracted and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((extendGearsElectroValve and aGearRetracted and timeout) implies x(g(anomaly)))

	//R71
	CTLSPEC ag((openDoorsElectroValve and not(doorsOpen) and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((openDoorsElectroValve and not(doorsOpen) and timeout) implies x(g(anomaly)))
	//R72
	CTLSPEC ag((closeDoorsElectroValve and not(doorsClosed) and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((closeDoorsElectroValve and not(doorsClosed) and timeout) implies x(g(anomaly)))
	//R73
	CTLSPEC ag((retractGearsElectroValve and not(gearsRetracted) and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((retractGearsElectroValve and not(gearsRetracted) and timeout) implies x(g(anomaly)))
	//R74
	CTLSPEC ag((extendGearsElectroValve and not(gearsExtended) and timeout) implies ax(ag(anomaly)))
	LTLSPEC g((extendGearsElectroValve and not(gearsExtended) and timeout) implies x(g(anomaly)))

	LTLSPEC g(anomaly implies g(anomaly)) //it's not possible to recover from anomaly
	CTLSPEC ag(anomaly implies ag(anomaly)) //it's not possible to recover from anomaly
	LTLSPEC f(not(anomaly))*/

	main rule r_Main =
		if not(anomaly) then
			par
				@original[]

				r_healthMonitoring[]
			endpar
		endif

default init s0:
	@original()

	function anomaly = false
