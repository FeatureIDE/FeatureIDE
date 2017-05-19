asm LandingGear


signature:
	enum domain LandingSet = {FRONT | LEFT | RIGHT}


	//sensors
	//gearsExtended is true if the corresponding gear is locked in the extended position and false in the other case
	dynamic monitored gearsExtended: LandingSet -> Boolean
	//gearsRetracted is true if the corresponding gear is locked in the retracted position and false in the other case
	dynamic monitored gearsRetracted: LandingSet -> Boolean
	//doorsClosed($s) is true if and only if the corresponding door is locked closed
	dynamic monitored doorsClosed: LandingSet -> Boolean
	//doorsOpen is true if and only if the corresponding door is locked open
	dynamic monitored doorsOpen: LandingSet -> Boolean
	//gearsShockAbsorber is true if and only if the aircfraft is on ground
	dynamic monitored gearsShockAbsorber: LandingSet -> Boolean

	derived gearsExtended: Boolean
	derived gearsRetracted: Boolean
	derived doorsClosed: Boolean
	derived doorsOpen: Boolean
	derived gearsShockAbsorber: Boolean

definitions:
	function gearsExtended = (forall $s in LandingSet with gearsExtended($s))
	function gearsRetracted = (forall $s in LandingSet with gearsRetracted($s))
	function doorsClosed = (forall $s in LandingSet with doorsClosed($s))
	function doorsOpen = (forall $s in LandingSet with doorsOpen($s))
	function gearsShockAbsorber = (forall $s in LandingSet with gearsShockAbsorber($s))



	/*
	JUSTICE gearsShockAbsorber
	//imposing the constraints on the single sensors is to weak 
	JUSTICE gearsExtended(FRONT)
	JUSTICE gearsExtended(LEFT)
	JUSTICE gearsExtended(RIGHT)
	JUSTICE gearsRetracted(FRONT)
	JUSTICE gearsRetracted(LEFT)
	JUSTICE gearsRetracted(RIGHT)
	JUSTICE doorsClosed(FRONT)
	JUSTICE doorsClosed(LEFT)
	JUSTICE doorsClosed(RIGHT)
	JUSTICE doorsOpen(FRONT)
	JUSTICE doorsOpen(LEFT)
	JUSTICE doorsOpen(RIGHT)
	JUSTICE gearsShockAbsorber(FRONT)
	JUSTICE gearsShockAbsorber(LEFT)
	JUSTICE gearsShockAbsorber(RIGHT)
	*/
	
default init s0:
	@original()