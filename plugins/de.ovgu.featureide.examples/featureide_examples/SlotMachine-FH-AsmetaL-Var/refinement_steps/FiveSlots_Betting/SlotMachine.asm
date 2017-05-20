asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm

signature:
	derived multFactor: Sign -> MultDomain
	
definitions:
domain BetDomain = {1..5}
domain MultDomain = {1..5}

	function multFactor($s in Sign) =
		switch($s)
			case BAR: 1
			case CHERRY: 2
			case DOLLAR: 3
			case SMILEY: 4
			case DYNAMITE: 5
		endswitch

	
		


