package basics.field;

import java.util.ArrayList;

public class GameField extends JPanel implements IPanelListener {
	private static final ArrayList<Integer> entityTypeList = new ArrayList<Integer>();
	static {
		addEntityType();
		entityTypeList.trimToSize();
	}
	
	/**
	 * Fügt dem Spiel neue Gegnertypen hinzu.
	 * Je öfter diese hinzugefügt werden, desto wahrscheinlicher erscheinen sie im Spiel.
	 * Folgende Gegner werden hinzu gefügt:
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	private static void addEntityType() {}
	
	public static IKIEntity getEnemy() {
		return LASTINSTANCE.enemy;
	}
	
	private IKIEntity enemy;
	private int countEntity = entityTypeList.size() + 1;
	
	/**
	 * Bestimmt zufällig einen neuen Gegner.
	 */
	private void createRandomEnemy() {
		if (--countEntity > 0) {
			enemy = newEntity(entityTypeList.get(rand.nextInt(entityTypeList.size())), rand.nextInt(4));
		} else {
			enemy = null;
		}
	}
	
	/**
	 * Erstellt einen neuen Gegner des gegebenen Typs.
	 * Folgende Gegner können erstellt werden:
	 * 
	 * @param type der Gegnertyp
	 * @param route der Richtung, in die sich der Gegner bewegt
	 * @return neue Instanz des Gegener
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	private IKIEntity newEntity(int type, int route) {
		return null;
	}
}