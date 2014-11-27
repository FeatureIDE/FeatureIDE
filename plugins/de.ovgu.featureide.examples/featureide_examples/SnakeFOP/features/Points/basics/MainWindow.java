package basics;

public class MainWindow extends JFrame {
	private int points = 0;

	/**
	 * Setzt eine neue Punktzahl.
	 * 
	 * @param points Punktzahl, die gesetzt werden soll
	 */
	public void addPoints(int points) {
		this.points += points;
	}

	/**
	 * Gibt die aktuelle Punktzahl zurück.
	 * 
	 * @return die aktuelle Punktzahl
	 */
	public int getPoints() {
		return points;
	}

	/**{@feature 0}
	 * Setzt die Punktzahl auf 0.
	 */
	public void startGame() {
		points = 0;
		original();
	}
}
