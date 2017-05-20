asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm

signature:
	domain BetDomain subsetof Integer
	domain MultDomain subsetof Integer
	dynamic monitored insertedMoney: BetDomain
	derived multFactor: Sign -> MultDomain
definitions:
	domain BetDomain = {1..3}
	domain MultDomain = {1..3}

	function multFactor($s in Sign) =
		switch($s)
			case BAR: 1
			case CHERRY: 2
			case DOLLAR: 3
		endswitch

	rule r_win($x in Sign) =
				par
					playerBudget := playerBudget + multFactor($x)*insertedMoney
					slotMachineBudget := slotMachineBudget - multFactor($x)*insertedMoney 
				endpar
				



