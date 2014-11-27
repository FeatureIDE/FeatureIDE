package entitys;

import java.util.Random;

import entitys.util.EntityHelpings;
import entitys.util.IKIEntity;
import basics.field.Level;
import basics.field.GameField;

/**
 * Klasse für eine Fliege.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 * @see IKIEntity
 */
public class Fly extends AEntity implements IKIEntity {
	private static final int maxEndurance = 35;
	
	private int endurance = 25;

	private int xPosAim;
	private int yPosAim;

	/**
	 * Creates a new instance of Fly.
	 * 
	 * @param xPosI
	 *            die xPosition
	 * @param yPosI
	 *            die yPosition
	 * @param routeI
	 *            die Richtung der Fly
	 */
	public Fly(int xPosI, int yPosI, int routeI) {
		super(xPosI, yPosI, routeI, 3);
	}

	/**
	 * Gibt Fly als String zurück um das Entity als Fly zu identifizieren.
	 * 
	 * @return Fly
	 */
	public int getType() {
		return IKIEntity.FLY;
	}
	
	@Override
	public void kill() {}
	
	@Override
	public boolean isAlive() {
		return head.isAlive;
	}	
	
	/**
	 * Lässt die Fliege sich erholen.
	 */
	private void relax() {
		if (endurance < maxEndurance) {
			++endurance;
		}
	}

	public boolean isPossibleToFly() {
		return endurance >= 30;
	}

	/**
	 * Lässt die Fliege wegfliegen.
	 * 
	 * @param level das Spielfeld
	 */
	public void flyAway(Level level) {
		head.status = 1;
		int[] position = EntityHelpings.walkableRandomFieldIndex();
		xPosAim = position[0] * (EntityHelpings.TILESIZE * GameField.getCurFactor()) + (4 * GameField.getCurFactor());
		yPosAim = position[1] * (EntityHelpings.TILESIZE * GameField.getCurFactor()) + (4 * GameField.getCurFactor());
		endurance = endurance - 30;
		if (Math.abs(head.xPos - xPosAim) >= Math.abs(head.yPos - yPosAim)) {
			if (head.xPos > xPosAim) {
				head.route = 3;
			} else {
				head.route = 1;
			}
		} else {
			if (head.yPos > yPosAim) {
				head.route = 0;
			} else {
				head.route = 2;
			}
		}
	}

	/**
	 * Gibt die aktuelle Ausdauer zurück.
	 * 
	 * @return Wert zwischen 0 und {@value #maxEndurance}
	 */
	public int getEndurance() {
		return endurance;
	}

	/**
	 * Lässt die Fliege rumlaufen.
	 * 
	 * @param field das Spielfeld
	 */
	public void walking(Level field) {
		relax();
		// die Bewegung beim rumfliegen
		if (head.getStatus() == 1) {
			if (field.getWalkableAbsolutPos(xPosAim, yPosAim) == false) {
				this.flyAway(field);
			} else {
				if (Math.abs(head.xPos - xPosAim) < (EntityHelpings.TILESIZE * GameField.getCurFactor())
						&& Math.abs(head.yPos - yPosAim) < (EntityHelpings.TILESIZE * GameField.getCurFactor())) {
					head.xPos = xPosAim;
					head.yPos = yPosAim;
					head.status = 0;
				} else {
					int dist = Math.abs(head.xPos - xPosAim)
							+ Math.abs(head.yPos - yPosAim);
					if (head.xPos > xPosAim) {
						head.xPos -= ((15 * GameField.getCurFactor()) * Math.abs(head.xPos - xPosAim) / dist);
					}
					if (head.yPos > yPosAim) {
						head.yPos -= ((15 * GameField.getCurFactor()) * Math.abs(head.yPos - yPosAim) / dist);
					}
					if (head.xPos < xPosAim) {
						head.xPos += ((15 * GameField.getCurFactor()) * Math.abs(head.xPos - xPosAim) / dist);
					}
					if (head.yPos < yPosAim) {
						head.yPos += ((15 * GameField.getCurFactor()) * Math.abs(head.yPos - yPosAim) / dist);
					}
				}
			}
		} else {
			oneStep(field);
		}
	}

	/**
	 * Eine Bewegung des Bug, in deier Methode wird der Laufstatus und die X-Y
	 * Positionsveränderrung gemacht.
	 * 
	 * @param field das Spielfeld
	 */
	public void oneStep(Level field) {
		think(field);
		moveHead();
	}
	
	private void think(Level field) {
		// ist auf einer Mittelpunktkreuzung und Random bereich
		if (field.isCenterOfTile(head.xPos) && field.isCenterOfTile(head.yPos)) {

			flyAway(field);
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

	/**
	 * Gibt zurück ob die Fliege fliegt.
	 * 
	 * @return
	 * 		{@code true}, wenn ja,
	 * 		{@code false} sonst
	 */
	public boolean isFlying() {
		return head.getStatus() == 1;
	}

	@Override
	public int getPoints() {
		return 50 + getEndurance();
	}
}
