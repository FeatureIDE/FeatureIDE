asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm

import ../../STDL/StandardLibrary
import ../../STDL/CTLlibrary
import ../../STDL/LTLlibrary

signature:
	domain BetDomain subsetof Integer
	domain MultDomain subsetof Integer
	dynamic monitored insertedMoney: BetDomain
	dynamic controlled slotMachineBudget: Money
	derived multFactor: Sign -> MultDomain

definitions:
	domain MultDomain = {1..3}
	domain BetDomain = {1..3}
	

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
				
	rule r_lose =
				par
					playerBudget := playerBudget - insertedMoney
					slotMachineBudget := slotMachineBudget + insertedMoney 
				endpar
		

	CTLSPEC ag(playerBudget + slotMachineBudget = 100)
	CTLSPEC ef(playerBudget = 23 and ex(playerBudget = 32))
	CTLSPEC eg(playerBudget >= 40 and playerBudget <= 60)

	main rule r_Main =
		if(playerBudget >= 3 and slotMachineBudget >= 9) then
			r_game[]
		endif


default init s0:
	function playerBudget = 50
	function slotMachineBudget = 50
