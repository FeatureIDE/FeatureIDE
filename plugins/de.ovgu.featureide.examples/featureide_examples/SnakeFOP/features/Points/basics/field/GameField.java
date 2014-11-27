package basics.field;

public class GameField extends JPanel implements IPanelListener {
	
	/**{@feature 0}
	 * Addiert die Punkte für das Essen des Gegners.
	 */
	private void killEntityPart(IKIEntity enemy, IEntityPart iEntityPart) {
		original(enemy, iEntityPart);
		main.addPoints(enemy.getPoints());
	}
	
	/**{@feature 0}
	 * @return Aktuelle Punktzahl als String.
	 */
	private String getGameStatusString() {
		return original() + "   Punkte: " + main.getPoints();
	}
}
