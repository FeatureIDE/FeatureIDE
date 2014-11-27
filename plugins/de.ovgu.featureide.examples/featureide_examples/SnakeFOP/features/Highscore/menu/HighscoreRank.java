package menu;

/**
 * Speichert den Namen und die zugehörigen Punkte.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see Highscore
 */
public class HighscoreRank {
	private final String name;
	private final int points;
	
	/**
	 * Erstellt einen neuen Highscore-Eintrag.
	 * 
	 * @param name Name zum zugehörigen Punktwert
	 * @param points Punkte die erreicht wurden
	 */
	public HighscoreRank(String name, int points) {
		this.name = name;
		this.points = points;
	}
	
	/**
	 * Gibt die Punkte zurück.
	 * 
	 * @return erreichte Punkte
	 */
	public int getPoints() {
		return points;
	}

	/**
	 * Gibt den Namen zurück.
	 * 
	 * @return Name des Highscore-Eintrags
	 */
	public String getName() {
		return name;
	}
	
	@Override
	public String toString() {
		return name + "\n" + points + "\n";
	}

}
