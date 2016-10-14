asm LandingGear

signature:
	enum domain LandingSet = {FRONT | LEFT | RIGHT}


	dynamic monitored gearsExtended: LandingSet -> Boolean
	dynamic monitored gearsRetracted: LandingSet -> Boolean
	dynamic monitored doorsClosed: LandingSet -> Boolean
	dynamic monitored doorsOpen: LandingSet -> Boolean
	dynamic monitored gearsShockAbsorber: LandingSet -> Boolean

	//gearsExtended is true if the corresponding gear is locked in the extended position and false in the other case
	derived gearsExtended: Boolean
	//gearsRetracted is true if the corresponding gear is locked in the retracted position and false in the other case
	derived gearsRetracted: Boolean
	//doorsClosed($s) is true if and only if the corresponding door is locked closed
	derived doorsClosed: Boolean
	//doorsOpen is true if and only if the corresponding door is locked open
	derived doorsOpen: Boolean
	//gearsShockAbsorber is true if and only if the aircfraft is on ground
	derived gearsShockAbsorber: Boolean

definitions:
	function gearsExtended = (forall $s in LandingSet with gearsExtended($s))
	function gearsRetracted = (forall $s in LandingSet with gearsRetracted($s))
	function doorsClosed = (forall $s in LandingSet with doorsClosed($s))
	function doorsOpen = (forall $s in LandingSet with doorsOpen($s))
	function gearsShockAbsorber = (forall $s in LandingSet with gearsShockAbsorber($s))


	rule r_closeDoor =
		/*@extend_original#doors*/ switch doors
			case CLOSING: /*compose#doors*/
				if doorsClosed then
					@original#doors
				endif
		endswitch



	//sono anche tradotti in proprietà CTL
	invariant over gears, doors: (gears = EXTENDING or gears = RETRACTING) implies doors = OPEN
	invariant over gears, doors: doors = CLOSED implies (gears = EXTENDED or gears = RETRACTED)



default init s0:
	@original()
	function doors = CLOSED
	function gears = EXTENDED
	function generalElectroValve = false
	function extendGearsElectroValve = false
	function retractGearsElectroValve = false
	function openDoorsElectroValve = false
	function closeDoorsElectroValve = false
