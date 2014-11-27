package basics.field;

public class GameField extends JPanel implements IPanelListener {
	private boolean snakeIsActivated = false;
	
	/**{@feature 1}
	 * Reagiert auf Eingaben des Spielers.
	 */
	private void snakeTurn() {
		if (!snake.getHoleArrived()) {
			final int nextRoute;
			switch (pushedKey) {
			case 37:
				nextRoute = 3;
				break;
			case 38:
				nextRoute = 0;
				break;
			case 39:
				nextRoute = 1;
				break;
			case 40:
				nextRoute = 2;
				break;
			default:
				nextRoute = -1;
				break;
			}
			
			if (snakeIsActivated == false) {
				snakeIsActivated = true;
				snake.setRoute(nextRoute);
			} else if (Math.abs(snake.getHead().getRoute() - nextRoute) != 2) {
				snake.setRoute(nextRoute);
			}
		}
	}
	
}
