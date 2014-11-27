package entitys;

import basics.field.Level;
import entitys.util.IKIEntity;

/**
 * Klasse für einen Käfer.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 * @see IKIEntity
 */
public class Bug extends AEntity implements IKIEntity {
	/**
	 * Erstellt einen neuen Käfer.
	 * 
	 * @param xPos die X-Position des Kopfs
	 * @param yPos die Y-Position des Kopfs
	 * @param route die Bewegungsrichtung am Anfang
	 */
	public Bug(int xPos, int yPos, int route) {
		super(xPos, yPos, route, 3);
	}
	
	public void oneStep(Level level) {
		head.status = (head.getStatus() + 1) % 4;
		if (level.isCenterOfTile(head.xPos) && level.isCenterOfTile(head.yPos)) {			
			final int oldRoute = head.route;
			head.route = rand.nextInt(8);
			if (!nextFieldWalkable(level)) {
				head.route = oldRoute;
			}
		}
		final int factor = (rand.nextBoolean()) ? 1 : -1;
		for (int i = 0; i < routeChange.length; ++i) {
			if (nextFieldWalkable(level)) {
				break;
			} else {
				head.route = (head.route + factor * routeChange[i] + 4) % 4;
			}
		}
		moveHead();
	}
	
	public void kill() {}

	public int getType() {
		return IKIEntity.BUG;
	}
	
	public boolean isAlive() {
		return head.isAlive;
	}
	
	public int getPoints() {
		return 30;
	}
}
