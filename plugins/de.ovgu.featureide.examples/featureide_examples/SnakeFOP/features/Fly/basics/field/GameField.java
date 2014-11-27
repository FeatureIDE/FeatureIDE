package basics.field;

import entitys.Fly;

public class GameField extends JPanel implements IPanelListener {
	
	/**{@feature 1}
	 * Fliege (1x)
	 */
	private static void addEntityType() {
		entityTypeList.add(IEntity.FLY);
		original();
	}
	
	/**{@feature 1}
	 * Fliege
	 */
	private IKIEntity newEntity(int type, int route) {
		IKIEntity enemy = original(type, route);
		if (enemy != null) {
			return enemy;
		} else if (type == IEntity.FLY) {
			int[] position = EntityHelpings.walkableRandomFieldIndex();
			return new Fly((position[0] * (SIZE * faktor)) + (4 * faktor),
					(position[1] * (SIZE * faktor)) + (4 * faktor), route);
		} else {
			return null;
		}
	}
}
