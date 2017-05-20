asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm


import ../../STDL/StandardLibrary
import ../../STDL/CTLlibrary
import ../../STDL/LTLlibrary

signature:
	enum domain Sign = {BAR | CHERRY | DOLLAR}
	domain Money subsetof Integer
	dynamic controlled playerBudget: Money
definitions:
domain Money = {1..100}

rule r_win = 
		playerBudget := playerBudget +2		

rule r_lose = 
		playerBudget := playerBudget -1

rule r_game =
		choose $x in Sign, $y in Sign, $z in Sign with true do
			if ($x = $y and $y = $z) then
			r_win[$x]
			else				
			r_lose[]	
			endif


CTLSPEC ef(playerBudget = 23 and ex(playerBudget = 25))
	main rule r_Main =
	
			r_game[]
		

default init s0:
function playerBudget = 50
