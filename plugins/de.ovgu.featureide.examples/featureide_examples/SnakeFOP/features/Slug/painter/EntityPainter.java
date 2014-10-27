package painter;

public class EntityPainter {
	// Slug Image Zeilen
	private int[] slugParts = {18, 12};
	
	/**{@feature 1}
	 * Gibt die Texturen einer Schnecke zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.SLUG) {
			return slugParts;
		} else {
			return original(entity);
		}
	}
}
