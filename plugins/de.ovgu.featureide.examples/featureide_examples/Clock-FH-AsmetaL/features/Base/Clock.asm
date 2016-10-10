/** at every step increments the seconds
*/
asm Clock

import ../../StandardLibrary

signature:
	domain Minute subsetof Integer
	domain Hour subsetof Integer

	controlled minutes: Minute
	controlled hours: Hour



definitions:
	domain Minute= {0..59}
	domain Hour = {0..23}

	macro rule r_IncHours =
		if minutes = 59 then
			hours := (hours + 1) mod 24
		endif

	main rule r_Main =
		par
			r_IncHours[]
			minutes := (minutes + 1) mod 60
		endpar



default init s0:
	function minutes = 0
	function hours = 0
