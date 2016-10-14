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
