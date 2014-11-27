package basics.field;

import entitys.Centipede;

public class GameField extends JPanel implements IPanelListener {
	
	/**{@feature 1}
	 * Tausendfüßler (1x)
	 */
	private static void addEntityType() {
		entityTypeList.add(IEntity.CENTIPEDE);
		original();
	}
	
	/**{@feature 1}
	 * Tausendfüßler
	 */
	private IKIEntity newEntity(int type, int route) {
		IKIEntity enemy = original(type, route);
		if (enemy != null) {
			return enemy;
		} else if (type == IEntity.CENTIPEDE) {
			int[] tmp = EntityHelpings.CentipedePos(route, 0);
			return new Centipede((tmp[0] * (SIZE * faktor))
					+ (4 * faktor), (tmp[1] * (SIZE * faktor))
					+ (4 * faktor), route, level);
		} else {
			return null;
		}
	}
}
