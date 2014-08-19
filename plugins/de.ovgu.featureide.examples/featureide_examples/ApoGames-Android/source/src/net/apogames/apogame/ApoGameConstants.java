package net.apogames.apogame;

public class ApoGameConstants {

	/*if[ApoSnake]*/
	public final static String USERLEVELS_GETPHP = "http://www.apo-games.de/apoSn4ke/get_level.php";
	public final static String USERLEVELS_SAVEPHP = "http://www.apo-games.de/apoSn4ke/save_level.php";
	
	public static final String PREFS_NAME = "ApoSnakePref";

	public static final boolean[] BUTTON_MENU = new boolean[] {
		true,
		true,
		/*if[UserLevels]*/
		true,
		/*else[UserLevels]*/
		false,
		/*end[UserLevels]*/
		/*if[LevelEditor]*/
		true,
		/*else[LevelEditor]*/
		false,
		/*end[LevelEditor]*/
		false, false, false, false, false, false, false, false, false};
	
	public static final boolean[] BUTTON_GAME = new boolean[] {false, false, false, false, false, true, false, false, false, false, false, false, false};
	public static final boolean[] BUTTON_PUZZLE = new boolean[] {false, false, false, false, true, false, false, false, false, false, false, false, false};
	
	/*if[LevelUpload]*/
	public static final boolean[] BUTTON_EDITOR = new boolean[] {false, false, false, false, false, false, true, true, true, true, true, true, true};
	/*else[LevelUpload]*/
	public static final boolean[] BUTTON_EDITOR = new boolean[] {false, false, false, false, false, false, true, true, false, true, true, true, true};
	/*end[LevelUpload]*/
	
	/*end[ApoSnake]*/
	
	/*if[ApoDice]*/
	public final static String USERLEVELS_GETPHP = "http://www.apo-games.de/apoDice4k/get_level.php";
	public final static String USERLEVELS_SAVEPHP = "http://www.apo-games.de/apoDice4k/save_level.php";
	
	public static final String PREFS_NAME = "ApoDicePref";

	public static final boolean[] BUTTON_MENU = new boolean[] {
		true,
		true,
		/*if[UserLevels]*/
		true,
		/*else[UserLevels]*/
		false,
		/*end[UserLevels]*/
		/*if[LevelEditor]*/
		true,
		/*else[LevelEditor]*/
		false,
		/*end[LevelEditor]*/
		false, false, false, false, false, false, false};
	
	public static final boolean[] BUTTON_GAME = new boolean[] {false, false, false, false, false, true, false, false, false, false, false};
	public static final boolean[] BUTTON_PUZZLE = new boolean[] {false, false, false, false, true, false, false, false, false, false, false};
	
	/*if[LevelUpload]*/
	public static final boolean[] BUTTON_EDITOR = new boolean[] {false, false, false, false, false, false, true, true, true, true, false};
	/*else[LevelUpload]*/
	public static final boolean[] BUTTON_EDITOR = new boolean[] {false, false, false, false, false, false, true, true, true, false, false};
	/*end[LevelUpload]*/
	
	/*end[ApoDice]*/
	
	public static final int GAME_WIDTH = 480;
	public static final int GAME_HEIGHT = 640;
	
	/*if[ApoSnake]*/
	public static final int NUM_BUTTONS = 13;
	/*end[ApoSnake]*/
	/*if[ApoDice]*/
	public static final int NUM_BUTTONS = 11;
	/*end[ApoDice]*/
}
