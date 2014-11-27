package entitys;

import basics.field.Level;
import entitys.util.EntityHelpings;

/**
 * Klasse für die Schlange.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 */
public class Snake extends AEntity {
	
	private boolean alreadyMoved = false;
	private boolean inHole = false;
	private boolean holearrived = false;

	/**
	 * Konstruktor einer neuen Snake.
	 * 
	 * Es wird eine neue Instanz der Klasse Snake erstellt.
	 * 
	 * @param xPosbeiStart
	 *            die X -Position der Snake beim Start
	 * @param yPosbeiStart
	 *            die Y -Position der Snake beim Start
	 * @param AnzahlderMittelteilebeimStart
	 *            die Anzahl der Elemente einer Snake zwischen Head und Tail
	 * 
	 */
	public Snake(int xPosbeiStart, int yPosbeiStart, int AnzahlderMittelteilebeimStart) {
		super(xPosbeiStart, yPosbeiStart, -1, EntityHelpings.TILESIZE);
		
		for (int i = 0; i <= AnzahlderMittelteilebeimStart; i++) {
			addPart(new EntityPart(xPosbeiStart, yPosbeiStart, -1));
		}
	}
	
	public int getType() {
		return 0;//IEntity.SNAKE;
	}
	
	private void setStatus(EntityPart first, EntityPart second) {
		if (first.getStatus() < 24) {
			int r1 = first.getRoute();
			int r2 = second.getRoute();
			
			if (Math.abs(r1 - r2) % 2 == 0) {
				if (r1 == -1) {
					first.status = 6;
				} else if (r1 % 2 == 0) {
					first.status = 4;
				} else {
					first.status = 5;
				}
			} else {
				switch (r1) {
				case 0: 
					switch (r2) {
					case 1: first.status = 11; break;
					case 3: first.status = 10; break;
					}
					break;
				case 1: 
					switch (r2) {
					case 0: first.status = 8; break;
					case 2: first.status = 10; break;
					}
					break;
				case 2: 
					switch (r2) {
					case 1: first.status = 9; break;
					case 3: first.status = 8; break;
					}
					break;
				case 3: 
					switch (r2) {
					case 0: first.status = 9; break;
					case 2: first.status = 11; break;
					}
					break;
				}
				
			}
		}
	}
	/**
	 * Verlängert die Schlange um ein Element.
	 */
	public void eat() {
		EntityPart neu = new EntityPart(tail.getXPos(), tail.getYPos(), tail.getRoute());
		neu.status = tail.getStatus();
		tail.status = 7;
		
		addPart(neu);
	}
	
	public void setRoute(int nextRoute) {
		head.route = nextRoute;
	}

	/**
	 * Verändert die Positionen der Eizelnen Elemente der Snake während eines Schrittes.
	 * 
	 * @param field das aktuelle Level
	 * @param countEntity Anzahl der verbleibenden Gegner
	 */
	public void oneStep(Level field, int countEntity) {
		if (head.getRoute() > -1) {
			alreadyMoved = true;
			
			field.setWalkableAbsolutPos(tail.getXPos(), tail.getYPos(), true);
			
			moveBody();
			EntityPart first = head;
			for (EntityPart second : head) {
				setStatus(first, second);
				first = second;
			}
			if (countEntity == 0 && head.xPos == field.getXStartSnake() && head.yPos == field.getYStartSnake()) {
				holearrived = true;
				if (tail.xPos == field.getXStartSnake()
						&& tail.yPos == field.getYStartSnake()) {
					inHole = true;
				}
			} else {
				field.setWalkableAbsolutPos(head.getXPos(), head.getYPos(), false);
				moveHead();
			}
		}
	}

	/**
	 * Gibt zurück ob sich die Schlange schon bewegt hat.
	 * 
	 * @return {@code true}, wenn die Schlange sich schon bewegt hat.
	 */
	public boolean alreadyMoved() {
		return alreadyMoved;
	}

	/**
	 * Gibt zurück, ob die Schlange schon vollkommen im Loch ist.
	 * 
	 * @return {@code true}, wenn die Schlange komplett im Loch ist.
	 */
	public boolean getInHole() {
		return inHole;
	}

	/**
	 * 
	 * Gibt zurück, ob die Schlange das Loch erreicht hat.
	 * 
	 * @return {@code true}, wenn die Schlange das Loch erreicht ist.
	 */
	public boolean getHoleArrived() {
		return holearrived;
	}
}
