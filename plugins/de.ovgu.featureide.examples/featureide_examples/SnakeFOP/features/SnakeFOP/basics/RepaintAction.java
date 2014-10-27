package basics;

import java.util.TimerTask;

import basics.field.GameField;

/**
 * Die Klasse bewirkt, dass in regelmäßigen Zeitabständen das Spielfeld
 * neu gezeichnet wird.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see MoveAction
 */
public class RepaintAction extends TimerTask {
	private final GameField gameField; // GameField welches aktualisiert werden soll

	/**
	 * Erstellt eine Instanz der Klasse.
	 * 
	 * @param gameField das aktuelle Spielfeld
	 */
	public RepaintAction(GameField gameField) {
		this.gameField = gameField;
	}
	
	@Override
	public void run() {
		gameField.repaint();
	}
}
