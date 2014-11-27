package basics;

import basics.field.GameField;
import basics.field.Level;
import menu.Highscore;

public class MainWindow extends JFrame {
	private final Highscore highscore = new Highscore();
	
	/**{@feature 0}
	 * Testet ob die aktuelle Punktzahl ein Highscore ist und leitet alles weitere ein.
	 */
	private void gameover() {
		points += lives * 1000;
		startMainMenu();
		if (highscore.setNewHighscore(getDifficulty(), points)) {
			startHighscore();
		}
	}
	
	/**
	 * Startet das Highscore-Menü.
	 */
	public void startHighscore() {
		infoTextArea.setText(highscore.getHighscoreFromDifficult(getDifficulty()));
		setVisibility(INFO);
	}
}
