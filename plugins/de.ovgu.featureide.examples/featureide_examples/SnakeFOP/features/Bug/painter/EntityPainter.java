package painter;

public class EntityPainter {
	// Bug Image Zeilen
	private int[] bugParts = {8, 9, 10, 11};

	/**{@feature 1}
	 * Gibt die Texturen eines Käfers zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.BUG) {
			return bugParts;
		} else {
			return original(entity);
		}
	}
}
