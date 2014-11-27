package entitys;

import basics.field.GameField;
import basics.field.Level;

public abstract class AEntity implements IEntity {
	
	/**
	 * Bewegt den Kopf der Entität in die aktuelle Richtung.
	 * 
	 * @see #moveBody()
	 */
	protected final void moveHead() {
		Level field = GameField.getCurLevel();
		int maxX = field.getMaxX() * field.getTileSize();
		int maxY = field.getMaxY() * field.getTileSize();
		switch (head.route) {
		case 0:
			head.yPos = (head.yPos - stepsize + maxY) % maxY;
			break;
		case 1:
			head.xPos = (head.xPos + stepsize) % maxX;
			break;
		case 2:
			head.yPos = (head.yPos + stepsize) % maxY;
			break;
		case 3:
			head.xPos = (head.xPos - stepsize + maxX) % maxX;
			break;
		default:
			break;
		}
	}
	
	/**
	 * Überprüft, ob das nächste Feld begehbar ist.
	 * 
	 * @param level das aktuelle Level
	 * 
	 * @return 
	 * 	{@code true} falls das Feld begehbar ist,</br>
	 * 	{@code false} falls nicht.
	 */
	protected final boolean nextFieldWalkable(Level level) {		
		final int stepsize = EntityHelpings.TILESIZE * GameField.getCurFactor();

		Level field = GameField.getCurLevel();
		int maxX = field.getMaxX() * field.getTileSize();
		int maxY = field.getMaxY() * field.getTileSize();
		
		switch (head.route) {
			case 0: return level.getWalkableAbsolutPos(head.xPos, (head.yPos - stepsize + maxY) % maxY);
			case 1: return level.getWalkableAbsolutPos((head.xPos + stepsize) % maxX, head.yPos);
			case 2: return level.getWalkableAbsolutPos(head.xPos, (head.yPos + stepsize) % maxY);
			case 3: return level.getWalkableAbsolutPos((head.xPos - stepsize + maxX) % maxX, head.yPos);
			default: return false;
		}
	}
}
