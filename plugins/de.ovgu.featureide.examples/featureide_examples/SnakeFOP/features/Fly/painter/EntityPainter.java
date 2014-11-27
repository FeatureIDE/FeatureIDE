package painter;

public class EntityPainter {
	// Fly Image Zeilen
	private int[] flyParts = {17, 17};
	
	/**{@feature 1}
	 * Gibt die Texturen einer Fliege zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.FLY) {
			return flyParts;
		} else {
			return original(entity);
		}
	}
}
