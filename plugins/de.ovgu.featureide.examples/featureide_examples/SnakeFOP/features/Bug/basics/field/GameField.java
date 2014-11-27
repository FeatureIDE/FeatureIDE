package basics.field;

import entitys.Bug;

public class GameField extends JPanel implements IPanelListener {
	
	/**{@feature 1}
	 * Käfer (2x)
	 */
	private static void addEntityType() {
		entityTypeList.add(IEntity.BUG);
		entityTypeList.add(IEntity.BUG);
		original();
	}
	
	/**{@feature 1}
	 * Käfer
	 */
	private IKIEntity newEntity(int type, int route) {
		IKIEntity enemy = original(type, route);
		if (enemy != null) {
			return enemy;
		} else if (type == IEntity.BUG) {
			int abs;
			int[] position;
			do {
				position = EntityHelpings.walkableRandomFieldIndex();
				final int dx = snake.getHead().getXPos() - (position[0] * SIZE * faktor);
				final int dy = snake.getHead().getYPos() - (position[1] * SIZE * faktor);
				abs = (int) Math.floor(Math.sqrt(dx * dx + dy * dy));
			} while (abs < 27);
			return new Bug(
					(position[0] * (SIZE * faktor)) + (4 * faktor),
					(position[1] * (SIZE * faktor)) + (4 * faktor),
					route);
		} else {
			return null;
		}
	}
}
