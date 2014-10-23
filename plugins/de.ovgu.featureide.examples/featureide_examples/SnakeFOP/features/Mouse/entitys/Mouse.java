package entitys;

import entitys.util.EntityHelpings;
import entitys.util.IEntityPart;
import entitys.util.IKIEntity;
import basics.field.Level;
import basics.field.GameField;

/**
 * Klasse für eine Maus.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 * @see IKIEntity
 */
public class Mouse extends AEntity implements IKIEntity {

	private static final int maxEndurance = 12;

	private int endurance = maxEndurance;
	private int rot = -1;

	/**
	 * Neue Instanz einer Maus.
	 * 
	 * @param xPos die X-Position auf dem Spielfeld
	 * @param yPos die Y-Position auf dem Spielfeld
	 * @param route die Bewegungsrichtung der Maus
	 */
	public Mouse(int route, int xPos, int yPos) {
		super(xPos, yPos, route, EntityHelpings.TILESIZE);
		
		moveHead();
		addPart(new EntityPart(xPos, yPos, route));

		head.status = 0;
		tail.status = 1;
	}

	/**
	 * 
	 * Gibt zurück das es sich bei den Entity um eine Mouse handelt.
	 * 
	 * @return Mouse
	 */
	public int getType() {
		return IKIEntity.MOUSE;
	}

	/**
	 * Simmuliert eine Bewegung.
	 * 
	 * @param field
	 *            das Spielfeld
	 */
	public void oneStep(Level field) {
		final Snake snake = GameField.getCurSnake();
		if (this.isAlive()) {
			// Entscheiden
//			doSomething = 0; // 0 bedeutet macht nichts
			final IEntityPart snakeHead = snake.getHead();
			int dist = EntityHelpings.getDist(snakeHead, head);
			if (dist <= 27) {
				if (endurance > 0) { // && snake.alreadyMoved()
					endurance--;
					// distanzen zur Schlange ermitteln
					int distFieldAbove = 0;
					int distFieldDown = 0;
					int distFieldLeft = 0;
					int distFieldRight = 0;
					
					final int stepsize = EntityHelpings.TILESIZE * GameField.getCurFactor();
					final EntityPart tmp = new EntityPart(head.xPos, head.yPos, head.route);
					if (head.yPos - stepsize > 0) {
						if (field.getWalkableAbsolutPos(head.xPos, head.yPos - stepsize)) {
							tmp.yPos -= stepsize;
							distFieldAbove = EntityHelpings.getDist(snakeHead, tmp);
							tmp.yPos += stepsize;
						}
					}
					if ((head.xPos + stepsize) / stepsize < field.getMaxX() - 1) {
						if (field.getWalkableAbsolutPos(head.xPos + stepsize, head.yPos)) {
							tmp.xPos += stepsize;
							distFieldRight = EntityHelpings.getDist(snakeHead, tmp);
							tmp.xPos -= stepsize;
						}
					}
					if ((head.yPos + stepsize) / stepsize < field.getMaxY() - 1) {
						if (field.getWalkableAbsolutPos(head.xPos, head.yPos + stepsize)) {
							tmp.yPos += stepsize;
							distFieldDown = EntityHelpings.getDist(snakeHead, tmp);
							tmp.yPos -= stepsize;
						}
					}
					if (head.xPos - stepsize > 0) {
						if (field.getWalkableAbsolutPos(head.xPos - stepsize, head.yPos)) {
							tmp.xPos -= stepsize;
							distFieldLeft = EntityHelpings.getDist(snakeHead, tmp);
							tmp.xPos += stepsize;
						}
					}
					
					if (distFieldAbove > distFieldRight && distFieldAbove > distFieldDown && distFieldAbove > distFieldLeft) {
						head.route = 0;
					} else if (distFieldRight > distFieldDown && distFieldRight > distFieldLeft) {
						head.route = 1;
					} else if (distFieldDown > distFieldLeft) {
						head.route = 2;
					} else if (distFieldDown < distFieldLeft) {
						head.route = 3;
					} else {
						return;
					}
					moveRoute();
				}
			} else if (rand.nextInt(3) == 0) {
				final int oldRoute = head.route;
				head.route = rand.nextInt(8);
				if (!nextFieldWalkable(field)) {
					head.route = oldRoute;
				}
				
				final int factor = (rand.nextBoolean()) ? 1 : -1;
				for (int i = 1; i < 3; ++i) {
					if (nextFieldWalkable(field)) {
						moveRoute();
						break;
					} else {
						head.route = (head.route + factor * i + 4) % 4;
					}
				}
			} else {
				relax();
			}
		} else {
			rot();
		}
	}

	private void moveRoute() {
		moveBody();
		moveHead();
	}

	/**
	 * Gibt zurück, ob die Mouse lebt.
	 * 
	 * @return
	 * 		{@code true}, wenn ja,</br>
	 * 		{@code false} sonst
	 */
	public boolean isAlive() {
		return head.isAlive && tail.isAlive;
	}

	/**
	 * Gibt zurück, ob der Kopf der Mouse noch existiert.
	 * 
	 * @return
	 * 		{@code true}, wenn ja,</br>
	 * 		{@code false} sonst
	 */
	public boolean headAlive() {
		return head.isAlive;
	}

	/**
	 * Gibt zurück, ob der Schwanz der Mouse noch existiert.
	 * 
	 * @return
	 * 		{@code true}, wenn ja,</br>
	 * 		{@code false} sonst
	 */
	public boolean tailAlive() {
		return tail.isAlive;
	}
	
	@Override
	public void kill() {
		for (EntityPart part : head) {
			part.status = 3;
		}
	}

	/**
	 * Lässt die Ausdauer der Mouse wieder regenerieren.
	 */
	private void relax() {
		if (endurance < maxEndurance) {
			endurance++;
		}
	}

	/**
	 * Lässt den Rest der Mouse verwesen.
	 */
	private void rot() {
		if (rot < 75) {
			rot++;
		}
	}

	/**
	 * Gibt die Zeit der Verwesung wieder.
	 * 
	 * @return die vergangene Zeit
	 */
	public int getRot() {
		return rot;
	}

	@Override
	public int getPoints() {
		if (isAlive()) {
			return 125;
		} else {
			return 75 - getRot();
		}
	}
}
