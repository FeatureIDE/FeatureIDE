asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm

signature:

	
	domain Money subsetof Integer
	dynamic controlled playerBudget: Money
	dynamic controlled slotMachineBudget: Money
	derived insertedMoney: Money

definitions:
	domain Money = {1..100}
	function insertedMoney = 1


	rule r_win($x in Sign) =
				par
					playerBudget := playerBudget + insertedMoney
					slotMachineBudget := slotMachineBudget - insertedMoney 
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
