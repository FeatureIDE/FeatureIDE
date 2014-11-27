package menu;

import menu.HighscoreRank;

/**
 * Verwaltung der Highscore-Werte.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see HighscoreRank
 */
public class Highscore {
	/**
	 * Anzahl der Highscore-Ränke je Schwierigkeitsstufe.</br>
	 * ({@value})
	 */
	public static final int numRanks = 3;
	/**
	 * Anzahl der Schwierigkeitsstufen.</br>
	 * ({@value})
	 */
	public static final int numDifficulties = 5;
	
	private final HighscoreRank[][] ranks = new HighscoreRank[numDifficulties][numRanks];

	/**
	 * Erstellt ein neues {@link Highscore}-Objekt und versucht die Highscore-Datei einzulesen.
	 */
	public Highscore() {
		loadHighscore();
	}

	/**
	 * Gibt die Highscoreliste der gewünschten Schwierigkeitsstufe zurück.
	 * 
	 * @param difficulty der Schwierigkeitsgrad, der angezeigt werden soll
	 * 
	 * @return Highscoreliste zur gegebenen Schwierigkeit als Text
	 */
	public String getHighscoreFromDifficult(int difficulty) {
		StringBuilder sb = new StringBuilder();
		HighscoreRank[] diffRanks = ranks[difficulty];
		for (int i = 0; i < diffRanks.length; ++i) {
			HighscoreRank rank = diffRanks[i];
			sb.append(i + 1);
			sb.append(".) ");
			sb.append(rank.getName());
			sb.append(" ");
			sb.append(rank.getPoints());
			sb.append("\n");
		}
		return sb.toString();
	}

	/**
	 * Prüft, ob ein neuer Highscore erricht wurde und setzt gegebenenfalls den neuen Highscore-Wert.
	 * 
	 * @param difficulty der Schwierigkeitsgrad in dem das Spiel gespielt wurde
	 * @param name der Name des Spielers
	 * @param newPoints die erreichten Punkte
	 * 
	 * @return
	 * 	{@code true} falls ein neuer Highscore erreicht wurde,</br>
	 * 	{@code false} falls nicht.
	 */
	public boolean setNewHighscore(int difficulty, String name, int newPoints) {
		HighscoreRank[] diffRanks = ranks[difficulty];
		boolean newHighScore = diffRanks[numRanks - 1].getPoints() < newPoints;
		
		if (newHighScore) {
			if (name == null || name.length() == 0) {
				name = "Name";
			} else {
				name.replace('\n', '_');
			}
			HighscoreRank newRank = new HighscoreRank(name, newPoints);
			for (int i = 0; i < diffRanks.length; ++i) {
				HighscoreRank oldRank = diffRanks[i];
				if (oldRank.getPoints() < newRank.getPoints()) {
					diffRanks[i] = newRank;
					newRank = oldRank;
				}
			}
			writeNewHighscore();
		}
		return newHighScore;
	}
	
	/**
	 * Prüft, ob ein neuer Highscore erreicht wurde und setzt gegebenenfalls den neuen Highscore-Wert.
	 * Setzt den Defaultnamen.
	 * 
	 * @param difficulty der Schwierigkeitsgrad in dem das Spiel gespielt wurde
	 * @param newPoints die erreichten Punkte
	 * 
	 * @return
	 * 	{@code true} falls ein neuer Highscore erreicht wurde,</br>
	 * 	{@code false} falls nicht.
	 */
	public boolean setNewHighscore(int difficulty, int newPoints) {
		
		return setNewHighscore(difficulty, null, newPoints);
	}

	/**
	 * Liest den Highscore aus der Highscore-Datei.
	 */
	private void loadHighscore() {
		String[] tmp = MyIO.readLines(MyIO.FILENAME_HIGHSCORE, Highscore.numDifficulties * Highscore.numRanks);
		
		if (tmp == null) {
			for (int i = 0; i < ranks.length; ++i) {
				HighscoreRank[] diffRanks = ranks[i];
				for (int j = 0; j < diffRanks.length; ++j) {
					diffRanks[j] = new HighscoreRank("Unknown", 0);
				}
			}
			return;
		}
		int count = 0;
		for (int i = 0; i < ranks.length; ++i) {
			HighscoreRank[] diffRanks = ranks[i];
			for (int j = 0; j < diffRanks.length; ++j) {
				diffRanks[j] = new HighscoreRank(tmp[count++], (int) Integer.parseInt(tmp[count++]));
			}
		}
	}

	/**
	 * Schreibt den neuen Highscore in die Highscore-Datei.
	 */
	private void writeNewHighscore() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < ranks.length; ++i) {
			HighscoreRank[] diffRanks = ranks[i];
			for (int j = 0; j < diffRanks.length; ++j) {
				sb.append(diffRanks[j]);
			}
		}
		MyIO.writeLines(MyIO.FILENAME_HIGHSCORE, sb.toString());
	}
}