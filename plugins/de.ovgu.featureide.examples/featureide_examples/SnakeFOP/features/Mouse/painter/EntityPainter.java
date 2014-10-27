package painter;

import entitys.Mouse;

public class EntityPainter {
	// Mouse Image Zeilen
	private int[] mouseParts = {13, 14, 15, 16};

	/**{@feature 0}
	 * Zeichnet eine Maus.
	 */
	private void paintEnemy(IEntity enemy) {
		if (enemy.getType() == IEntity.MOUSE) {
			paintMouse((Mouse) enemy);
		} else {
			original(enemy);
		}
	}
	
	/**{@feature 1}
	 * Gibt die Texturen einer Maus zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.MOUSE) {
			return mouseParts;
		} else {
			return original(entity);
		}
	}
	
	private void paintMouse(Mouse mouse) {
		if (mouse.isAlive()) {
			int count = 0;
			for (IEntityPart iEntityPart : mouse) {
				bigPicturePaint(iEntityPart.getRoute(), mouseParts[count++], iEntityPart.getXPos(),
						iEntityPart.getYPos());
			}
		} else {
			int count = 2;
			for (IEntityPart iEntityPart : mouse) {
				if (count == 2 && mouse.headAlive()) {
					bigPicturePaint(iEntityPart.getRoute(), mouseParts[count],
							iEntityPart.getXPos(), iEntityPart.getYPos());
				} else if (count == 3 && mouse.tailAlive()) {
					bigPicturePaint(iEntityPart.getRoute(), mouseParts[count],
							iEntityPart.getXPos(), iEntityPart.getYPos());
				}
				count++;
			}
		}
	}
}
