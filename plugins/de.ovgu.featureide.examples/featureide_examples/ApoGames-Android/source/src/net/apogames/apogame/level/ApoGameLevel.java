package net.apogames.apogame.level;

public class ApoGameLevel {

	/*if[ApoSnake]*/
	/**
	 * 0 = free
	 * 1 = head red left
	 * 2 = head red down
	 * 3 = head red right
	 * 4 = head red up
	 * 5 = red coin
	 * 6 = red wall
	 * 7 = head blue left
	 * 8 = head blue down
	 * 9 = head blue right
	 * a = head blue up
	 * b = blue coin
	 * c = blue wall
	 * d = head green left
	 * e = head green down
	 * f = head green right
	 * g = head green up
	 * h = green coin
	 * i = green wall
	 * 
	 * 19 = rot Wand (ex Schlange)
	 * 20 = blau Wand (ex Schlange)
	 * 21 = grüne Wand (ex Schlange)
	 */
	private static final String[] levelsString = new String[] {
		
		/*if[DemoLevels]*/
		
			"de"+
			"0000"+
			"0660"+
			"0650"+
			"0666"+
			"0001",
		
//			"de"+
//			"5555"+
//			"0666"+
//			"5005"+
//			"6660"+
//			"3555",
			
			"ed"+
			"56000"+
			"56b65"+
			"06060"+
			"0h064",
			
			"gd"+
			"5056b0b"+
			"0606060"+
			"0606660"+
			"4650b6b",
			
			"ee"+
			"50005"+
			"06560"+
			"05450"+
			"06560"+
			"50005",
			
			"cchi5c36b5b",
			
		/*end[DemoLevels]*/
		/*if[StandardLevels]*/
			
			"cf"+
			"0bc"+
			"0c0"+
			"bab"+
			"545"+
			"060"+
			"650",

			"ddebbb6ii656b5b65i",
			
//			"ge"+
//			"00bcb0b"+
//			"0ccccc0"+
//			"00b666b"+
//			"ccccbcb"+
//			"000646a",
			
			"efcihiccccccbiiibbigibiiiiibbabb",
			
			"fhb000000ccccc0cbbbb0cbc2b0cbabb0cb6bb00ccc50cbbbb",
			
			"gg00c0c000hhhhh0chihihc0hhghh0chihihc0hhhhh000c0c00",
			
			"eg"+
			"05450"+
			"06660"+
			"06060"+
			"05550"+
			"5ccc5"+
			"66566"+
			"06460",
			
			"ggh60006h60i0i0660ihi0650hgh0560ihi0660i0i06h60006h",	

			"ee5i5cb6i6c6hi5c56i6c6hi5c4",
			
			"gghcbbbchhc666chhc646chhc666chhcbabchhccccchicbbbci",
			
			"hc"+
			"06b60c5c"+
			"b5456b0b"+
			"06b60c5c",
			
			"ee5b5b6b5b6b5b6b566b5bg65b5",
			
			"dffh655h666655b6546666ihhh",
			
			"eeh25bhb6i659cbc7hi6ib5bhg5",
			
			"cjch15ch9bchc5cbd5ch3bchc5ch75ch",
			
			"edcccechcbchcc6h00h4i5",
			
			/*end[StandardLevels]*/
			/*if[ProLevels]*/
			
			"eebh5b65666bc626hcb6hiabihi",
			
			"ggbhb5hbhh8iciebbciciihh66666bbcc6cchh6c4c6bbh555bh",
			
			"ic65chc5chi3c5bcb5cd6hc5chc5i",
			
			"hechb565hb566cbi61h5iib6c7bbbcbi6dh665hbbi",
			
			"ee05cb00hc50cc20b59c560ihih",
			
			"fe"+
			"b555bc"+
			"b565bc"+
			"b455ac"+
			"h666ch"+
			"i6555i",
			
			"fd855558b6ii6b55cc555h665h",
			
			"ghibehicbbb656bhbiei6bib666bcbb666bcb0cac6hhb06bcbbcba0ci5",
			
			"ehc666i6bbb6hacb56bbb5hi6i56b6b4h626icb6bi",
			
			"fe"+
			"c5c556"+
			"cbbcii"+
			"h6b6ie"+
			"h4a5ii"+
			"h655bb",
			/*end[ProLevels]*/
	};
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	/**
	 * 0 = empty
	 * 1 = goal
	 * 2 = dice with no moves
	 * 3 = dice with 1 moves
	 * 4 = dice with 2 moves
	 * 5 = dice with 3 moves
	 * 6 = dice with 4 moves
	 * 7 = dice with 5 moves
	 * 8 = dice with 6 moves
	 * a = dice with no moves and goal down
	 * b = dice with 1 moves and goal down
	 * c = dice with 2 moves and goal down
	 * d = dice with 3 moves and goal down
	 * e = dice with 4 moves and goal down
	 * f = dice with 5 moves and goal down
	 * g = dice with 6 moves and goal down
	 */
	private static final String[] levelsString = new String[] {
		/*if[DemoLevels]*/
		
		"00000000"+
		"00000000"+
		"04000050"+
		"00100000"+
		"00000100"+
		"00310000"+
		"00000000"+
		"00000000",
		
		"0000000000000000000000000040000000311000000000000000000000000000",
		
		"00000000" +
		"00000000" +
		"00000000" +
		"00040000" +
		"00103000" +
		"00010000" +
		"00000000" +
		"00000000",
		
		"0000000000000000000000000013100000000000004150000000000000000000",
		
		"00000000"+
		"00000000"+
		"00031000"+
		"00041000"+
		"00015000"+
		"00016000"+
		"00000000"+
		"00000000",
		
		/*end[DemoLevels]*/
		/*if[StandardLevels]*/

		"00000000"+
		"00000000"+
		"00000000"+
		"00041400"+
		"00000000"+
		"00015100"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"00005000"+
		"00611000"+
		"00011400"+
		"00030000"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"00014100"+
		"00004000"+
		"00311130"+
		"00005000"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"00016100"+
		"00041000"+
		"00001400"+
		"00006000"+
		"00000000"+
		"00000000",
		
		"00500300"+
		"00100100"+
		"00064000"+
		"00011000"+
		"04000040"+
		"03111130"+
		"00000000"+
		"00000000",
		
		"0000000000000000000000000001100000311300043113400000000000000000",
		
		"0000000000000000000110000031150000400400005003000001100000000000",
		
		"00000000"+
		"00503050"+
		"00011100"+
		"00310130"+
		"00011100"+
		"00503050"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"00000000"+
		"00010500"+
		"00061000"+
		"00010500"+
		"00000000"+
		"00000000",
		
		"00000000000000000005000000040000011b1100000400000005000000000000",
		
		"00000000"+
		"00000000"+
		"00054000"+
		"00411500"+
		"00145100"+
		"00011000"+
		"00000000"+
		"00000000",
		
		"0000000000000000000300000031100000010140000015000000400000000000",
		
		"0000000000000000004131000010040000300100001415000000000000000000",
		
		"0000000000000000000400000031300004111400000100000000000000000000",
		
		"0000000000431000003110000011330003311000001130000013400000000000",
		
		/*end[StandardLevels]*/
		/*if[ProLevels]*/
		
		"0000000000000000003b0c40000101000004430000b000b00001110000000000",
		
		"0000000000014000001315000131514004151310005131000004100000000000",
		
		"0000000000000000041814000161610008101800016161000418140000000000",
		
		"0000000000140000005100000013150000416100000014000000510000000000",
		
		"00000000"+
		"00013400"+
		"00151540"+
		"00111440"+
		"00113050"+
		"00011300"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00413160"+
		"00100010"+
		"00361030"+
		"00100010"+
		"00613140"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"00050100"+
		"00001500"+
		"00015000"+
		"00100000"+
		"00000000"+
		"00005000",
		
		"00000000"+
		"01030000"+
		"00500100"+
		"00107000"+
		"06001000"+
		"00010400"+
		"00000000"+
		"00000000",
		
		"00000000"+
		"00000000"+
		"10401030"+
		"0d0e0d00"+
		"30104010"+
		"00000000"+
		"00000000"+
		"00000000",
		
		"00040000"+
		"00000000"+
		"00d1d000"+
		"301b1030"+
		"00e1e000"+
		"00000000"+
		"00040000"+
		"00000000",
		/*end[ProLevels]*/
	};
	/*end[ApoDice]*/
	
	public static String[] editorLevels = null;
	
	public static final String getLevel(int level) {
		if ((level < 0) || (level >= levelsString.length)) {
			return null;
		}
		return levelsString[level];
	}
	
	public static final int MAX_LEVELS = levelsString.length;
	
	public static boolean isIn(String level) {
		for (int i = 0; i < levelsString.length; i++) {
			if (level.equals(levelsString[i])) {
				return true;
			}
		}
		return false;
	}
}
