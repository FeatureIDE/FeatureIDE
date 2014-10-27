package entitys;

import basics.field.Level;
import entitys.util.IKIEntity;

/**
 * Klasse für eine Schnecke.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 * @see IKIEntity
 */
public class Slug extends AEntity implements IKIEntity {
	private static final int maxSlimeLength = 12;
	private int slimeLength = 0;

	/**
	 * Neue Instanz einer Schnecke.
	 * 
	 * @param xPos die X-Position auf dem Spielfeld
	 * @param yPos die Y-Position auf dem Spielfeld
	 * @param route die Bewegungsrichtung der Schnecke
	 */
	public Slug(int xPos, int yPos, int route) {
		super(xPos, yPos, route, 3);
	}
	
	public int getPoints() {
		return 30;
	}
	
	public int getType() {
		return IKIEntity.SLUG;
	}
	
	public boolean isAlive() {
		return head.isAlive;
	}
	
	public void kill() {}
	
	public void oneStep(Level field) {
		think(field);
		if (slimeLength < maxSlimeLength - 1) {
			EntityPart newPart = new EntityPart(tail.xPos, tail.yPos, tail.route);
			newPart.isAlive = false;
			newPart.status = 1;
			addPart(newPart);
			++slimeLength;
		}
		moveBody();
		moveHead();
	}

	private void think(Level field) {
		if (field.isCenterOfTile(head.getXPos()) && field.isCenterOfTile(head.getYPos())) {
			final int oldRoute = head.route;
			head.route = rand.nextInt(8);
			if (!nextFieldWalkable(field)) {
				head.route = oldRoute;
			}
		}
		final int factor = (rand.nextBoolean()) ? 1 : -1;
		for (int i = 0; i < routeChange.length; ++i) {
			if (nextFieldWalkable(field)) {
				break;
			} else {
				head.route = (head.route + factor * routeChange[i] + 4) % 4;
			}
		}
	}	
}
