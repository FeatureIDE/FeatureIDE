package menu;

public class MainMenu extends JPanel implements IPanelListener {
	private static int highscoreIndex = - 1;
	
	/**{@feature 0}
	 * Highscore.
	 */
	private static void addMenuElements() {
		original();
		menuElements.add("Highscore");
		highscoreIndex = menuElements.size() - 1;
	}
	
	/**{@feature 1}
	 * Highscore Menüpunkt. 
	 */
	private void testOtherMenuPoints() {
		if (selected == highscoreIndex) {
			main.startHighscore();
		} else {
			original();
		}
	}
	
}
