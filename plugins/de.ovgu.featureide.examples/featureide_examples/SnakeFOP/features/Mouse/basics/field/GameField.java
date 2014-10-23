package basics.field;

import entitys.Mouse;

public class GameField extends JPanel implements IPanelListener {
	
	/**{@feature 1}
	 * Maus (1x)
	 */
	private static void addEntityType() {
		entityTypeList.add(IEntity.MOUSE);
		original();
	}
	
	/**{@feature 1}
	 * Maus
	 */
	private IKIEntity newEntity(int type, int route) {
		IKIEntity enemy = original(type, route);
		if (enemy != null) {
			return enemy;
		} else if (type == IEntity.MOUSE) {
			int[] tmp = EntityHelpings.mousePos(route);
			return new Mouse(route, (tmp[0] * (SIZE * faktor))
					+ (4 * faktor), (tmp[1] * (SIZE * faktor))
					+ (4 * faktor));
		} else {
			return null;
		}
	}
}
