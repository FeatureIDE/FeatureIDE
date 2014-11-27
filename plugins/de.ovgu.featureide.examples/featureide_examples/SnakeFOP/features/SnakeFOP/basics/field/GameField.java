package basics.field;

import java.awt.Color;
import java.awt.Graphics;
import java.util.Random;

import javax.swing.JPanel;

import basics.MainWindow;
import basics.util.IPanelListener;
import entitys.Snake;
import entitys.util.EntityHelpings;
import entitys.util.IEntity;
import entitys.util.IEntityPart;
import entitys.util.IKIEntity;

/**
 * Durch diese Klasse wird das Spielfeld erzeugt und auf dem Display angezeigt.
 * Die Methode {@link #move()} wird durch die Klasse {@link MoveAction} immer wieder erneut
 * aufgerufen.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 */
public class GameField extends JPanel implements IPanelListener {
	private static final long serialVersionUID = 1L;

	private static final String[] menuElements = { "Weiter", "Menü", "Ende" };
	private static final int numberMenuPoints = menuElements.length;
	private static final int SIZE = 9;

	private static GameField LASTINSTANCE = null;

	public static int getCurFactor() {
		return LASTINSTANCE.faktor;
	}
	public static Level getCurLevel() {
		return LASTINSTANCE.level;
	}

	public static Snake getCurSnake() {
		return LASTINSTANCE.snake;
	}
	private int faktor = 1;

	private boolean startMenu = false;
	private boolean booleanToFastPushed = false;

	private int toFastPushed = -1;
	private MainWindow main;
	private int center = 0;

	private int selectedMenuPoint = 0;
	
	private boolean backroundRepaint = true;

	private boolean forbitPaintAction = false;

	private final Level level; // field das dargestellt wird

	private Snake snake;
	private final Random rand = new Random();
	private int pushedKey = -1;

	/**
	 * Konstruktor eines Neuen Levels.
	 * 
	 * @param main
	 *            Main von der alles gesteuert wird
	 * @param level
	 *            Field aus dem das Level besteht
	 */
	public GameField(MainWindow main, Level level) {
		LASTINSTANCE = this;

		faktor = level.getTileSize() / SIZE;
		forbitPaintAction = false;
		this.main = main;
		main.getPainter().newLevel();
		
		center = 150;// getHeight()/2;
		
		this.level = level;// new Field("/level/level3.dat");
		
		snake = new Snake(level.getXStartSnake(), level.getYStartSnake(), 5);
		createRandomEnemy();
		
		repaint();
	}

	public void keyPressed(int arg0) {
		int code = arg0;
		if ((code >= 37 && code <= 40) || code == 80 || code == 10) {
			if (!forbitPaintAction) {
				if (booleanToFastPushed && !startMenu) {
					toFastPushed = arg0;
				} else {
					pushedKey = arg0;
					if (!startMenu && pushedKey != 80 && pushedKey != 10) {
						booleanToFastPushed = true;
					}
				}
				if (pushedKey == 80 || pushedKey == 10) {
					if (!startMenu) {
						MenueStart();
					}
				}
				if (startMenu) {
					repaint();
				}
			}
		}
	}

	/**
	 * Lässt alle Entitäten sich bewegen.
	 */
	public void move() {
		if (!startMenu) {
			if (isSnakeAlive()) {
				if (pushedKey != -1) {
					snakeTurn();
					booleanToFastPushed = false;
				}

				// bewegen der Entitys
//				if (xyz++ % 2 == 0)
				snake.oneStep(level, countEntity);
				if (snake.getInHole()) {
					forbitPaintAction = true;
					main.runningNextLevel(true);
				}

				if (enemy != null) {
					enemy.oneStep(level);
					if (snake.alreadyMoved()) { //&& snakeIsActivated) {
						for (IEntityPart iEntityPart : enemy) {
							if (iEntityPart.isAlive()) { //iEntityPart.isEatable() && 
								final int test = EntityHelpings.getDist(snake.getHead(), iEntityPart);

								if (test < (5 * faktor)) {
//									if (enemy.getType() == EntityType.FLY && ((Fly) enemy).isFlying()) {
//										continue;
//									}
									killEntityPart(enemy, iEntityPart);
								}
							}
						}
						boolean completlyEaten = true;
						for (IEntityPart iEntityPart : enemy) {
							if (iEntityPart.isAlive()) {
								completlyEaten = false;
								break;
							}
						}
						if (completlyEaten) {
							if (countEntity != 0) {
								createRandomEnemy();
							}
						}
					}
				}
				pushedKey = -1;
			} else {// tod
				forbitPaintAction = true;
				main.runningNextLevel(false);
			}
		}
	}
	
	/**
	 * Wird aufgerufen, wenn der Kopf der Schlange ein Teil eines Gegners brührt.
	 * 
	 * @param enemy der Gegner
	 * @param iEntityPart des Teilstück des Gegners
	 */
	/**{@feature 0}
	 * Tötet das Teilstück des Gegners und den Gegner.
	 */
	private void killEntityPart(IKIEntity enemy, IEntityPart iEntityPart) {
		if (enemy.isAlive()) {
			enemy.kill();
		}
		iEntityPart.eat();
		snake.eat();
	}
	/**
	 * Gibt den aktuellen Spielstand zurück.
	 * 
	 * @return aktueller Spielstand als String
	 */
	/**{@feature 0}
	 * @return Anzahl der übrigen Leben.
	 */
	private String getGameStatusString() {
		return "Leben: " + main.getLives();
	}

	/**
	 * Malt die Einzelnen Frames mit allen Info-Elementen.
	 * 
	 * @param g Graphics-Objekt, auf dem gemalt wird
	 */
	public void paint(Graphics g) {
		if (main.hasFocus()) {
			int xwidth = level.getMaxX() * main.getElementSize();
			int xheight = level.getMaxY() * main.getElementSize();
			if (!forbitPaintAction) {

				if (backroundRepaint) {
					backroundRepaint = false;
					main.getPainter().newLevel();
				}
				// statusangaben über eigentlichem Spielfeld
				g.fillRect(0, 0, xwidth, xheight - 40); // macht hintergrund
														// schwarz
				g.setColor(Color.GREEN);
				g.drawString(getGameStatusString(), 0, 10);

				g.clearRect(0, 20, 1000, 1000);
				g.drawImage(main.getPainter().paintFrame(level, new IEntity[] { snake, enemy }), 0, 20, xwidth, xheight + 20, 0, 0,
						level.getMaxX() * SIZE * faktor, level.getMaxY()
								* SIZE * faktor, null);

				// Menue bei Spielpause
				if (startMenu) {
					menu();
					g.setColor(Color.RED);
					g.drawString(menuElements[(selectedMenuPoint
							+ numberMenuPoints - 1)
							% numberMenuPoints], 20, center - 20 + 10);
					g.drawString(menuElements[(selectedMenuPoint + 1)
							% numberMenuPoints], 20, center + 20 + 10);
					g.setColor(Color.WHITE);
					// g.setColor(255,255,255);
					g.fillRect(0, center - 2, xwidth, 18);
					g.setColor(Color.RED);
					g.drawLine(0, center - 2, xwidth, center - 2);
					g.drawLine(0, center - 3, xwidth, center - 3);
					g.drawLine(0, center + 15, xwidth, center + 15);
					g.drawLine(0, center + 16, xwidth, center + 16);
					g.drawString(menuElements[(selectedMenuPoint)
							% numberMenuPoints], 20, center + 10);
				}

				if (toFastPushed != -1) {
					pushedKey = toFastPushed;
					toFastPushed = -1;
				}
			}
		}
	}
	
	/**
	 * Testet ob die Schlange noch am Leben ist.
	 * 
	 * @return boolean noch am Leben?
	 */
	private boolean isSnakeAlive() {
		final int snakeX = snake.getHead().getXPos();
		if (snakeX < 0) {
			return false;
		}
		final int snakeY = snake.getHead().getYPos();
		if (snakeY < 0) {
			return false;
		}
		if (snakeX > level.getMaxX() * (SIZE * faktor)) {
			return false;
		}
		if (snakeY > level.getMaxY() * (SIZE * faktor)) {
			return false;
		}
		if (!snake.getHoleArrived()) {
			if (level.getWalkableAbsolutPos(snakeX , snakeY) == false) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Verarbeitet die gedrückten Tasten wenn man sich im Menue befindet
	 */
	private void menu() {
		if (pushedKey == 38) {// oben
			selectedMenuPoint = (selectedMenuPoint + numberMenuPoints - 1) % numberMenuPoints;
		} else if (pushedKey == 40) {// unten
			selectedMenuPoint = (selectedMenuPoint + 1) % numberMenuPoints;
		} else if (pushedKey == 80 || pushedKey == 10) {// bestätigen
			switch (selectedMenuPoint) {
			case 0:
				startMenu = false;
				pushedKey = -1;
				main.setBreak(true);
				break;
			case 1:
				main.startMainMenu();
				forbitPaintAction = true;
				break;
			case 2:
				main.exit();
				break;
			}
			repaint();
		}
	}

	private void MenueStart() {
		main.setBreak(false);
		startMenu = true;
		pushedKey = -2;
		repaint();
	}

	/**
	 * Dreht die Schlange.
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	private void snakeTurn() {
	}
	
}
