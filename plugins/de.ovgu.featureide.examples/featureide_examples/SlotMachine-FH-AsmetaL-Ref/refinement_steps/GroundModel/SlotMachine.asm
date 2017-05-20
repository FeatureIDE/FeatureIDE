asm SlotMachine
//adapted from garganti, parcaini, scandurra, silviabonfanti, https://sourceforge.net/p/asmeta/code/HEAD/tree/asm_examples/examples/slotMachine.asm


import ../../STDL/StandardLibrary
import ../../STDL/CTLlibrary
import ../../STDL/LTLlibrary

signature:
	enum domain Sign = {BAR | CHERRY | DOLLAR}

definitions:


rule r_win($x in Sign) = 
		skip	

rule r_lose = 
		skip
		
rule r_game =
		choose $x in Sign, $y in Sign, $z in Sign with true do
			if ($x = $y and $y = $z) then
			r_win[$x]
			else				
			r_lose[]	
			endif

	main rule r_Main =
	
			r_game[]
		

default init s0:
