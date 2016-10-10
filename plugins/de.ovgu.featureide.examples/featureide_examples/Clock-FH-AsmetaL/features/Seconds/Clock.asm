/** at every step increments the seconds
*/
asm Clock

import ../../StandardLibrary

signature:
	domain Second subsetof Integer

	controlled seconds: Second

definitions:
	domain Second = {0..59}

	macro rule r_IncHours =
		par
			@original[]
			if seconds = 59 then
				minutes := (minutes + 1) mod 60
			endif
		endpar


	main rule r_Main =
		par
			r_IncHours[]
			seconds := (seconds + 1) mod 60
		endpar



default init s0:
	function seconds = 0
	function minutes = 0
	function hours = 0
