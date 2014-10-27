package entitys;

public abstract class AEntity implements IEntity {
	
	/**{feature 1}
	 * Vor dem Aufruf sollte überpüft werden, ob die Entität das Spielfeld verlässt.
	 */
	protected final void moveHead() {
		switch (head.route) {
		case 0:
			head.yPos -= stepsize;
			break;
		case 1:
			head.xPos += stepsize;
			break;
		case 2:
			head.yPos += stepsize;
			break;
		case 3:
			head.xPos -= stepsize;
			break;
		default:
			break;
		}
	}
	
	/**{@general 1}
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
		
		switch (head.route) {
			case 0: return head.yPos - stepsize >= 0 && level.getWalkableAbsolutPos(head.xPos, head.yPos - stepsize);
			case 1: return head.xPos + stepsize < level.getMaxX() * stepsize && level.getWalkableAbsolutPos(head.xPos + stepsize, head.yPos);
			case 2: return head.yPos + stepsize < level.getMaxY() * stepsize && level.getWalkableAbsolutPos(head.xPos, head.yPos + stepsize);
			case 3: return head.xPos - stepsize >= 0 && level.getWalkableAbsolutPos(head.xPos - stepsize, head.yPos);
			default: return false;
		}
	}
}
