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

import java.util.ArrayList; 

import entitys.Centipede; 

public   class  GameField  extends JPanel  implements IPanelListener {
	
	private static final long serialVersionUID = 1L;

	

	private static final String[] menuElements = { "Weiter", "Men�", "Ende" };

	
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

	

	private final Level level;

	 // field das dargestellt wird

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
	 * L�sst alle Entit�ten sich bewegen.
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
	 * Wird aufgerufen, wenn der Kopf der Schlange ein Teil eines Gegners br�hrt.
	 * 
	 * @param enemy der Gegner
	 * @param iEntityPart des Teilst�ck des Gegners
	 */
	/**{@feature 0}
	 * T�tet das Teilst�ck des Gegners und den Gegner.
	 */
	 private void  killEntityPart__wrappee__SnakeFOP  (IKIEntity enemy, IEntityPart iEntityPart) {
		if (enemy.isAlive()) {
			enemy.kill();
		}
		iEntityPart.eat();
		snake.eat();
	}

	
	
	/**{@feature 0}
	 * Addiert die Punkte f�r das Essen des Gegners.
	 */
	private void killEntityPart(IKIEntity enemy, IEntityPart iEntityPart) {
		killEntityPart__wrappee__SnakeFOP(enemy, iEntityPart);
		main.addPoints(enemy.getPoints());
	}

	
	/**
	 * Gibt den aktuellen Spielstand zur�ck.
	 * 
	 * @return aktueller Spielstand als String
	 */
	/**{@feature 0}
	 * @return Anzahl der �brigen Leben.
	 */
	 private String  getGameStatusString__wrappee__SnakeFOP  () {
		return "Leben: " + main.getLives();
	}

	
	
	/**{@feature 0}
	 * @return Aktuelle Punktzahl als String.
	 */
	private String getGameStatusString() {
		return getGameStatusString__wrappee__SnakeFOP() + "   Punkte: " + main.getPoints();
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
				// statusangaben �ber eigentlichem Spielfeld
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
	 * Verarbeitet die gedr�ckten Tasten wenn man sich im Menue befindet
	 */
	private void menu() {
		if (pushedKey == 38) {// oben
			selectedMenuPoint = (selectedMenuPoint + numberMenuPoints - 1) % numberMenuPoints;
		} else if (pushedKey == 40) {// unten
			selectedMenuPoint = (selectedMenuPoint + 1) % numberMenuPoints;
		} else if (pushedKey == 80 || pushedKey == 10) {// best�tigen
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

	
	
	/**{@feature 1}
	 * Reagiert auf Eingaben des Spielers.
	 */
	private void snakeTurn  () {
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

	
	private static final ArrayList<Integer> entityTypeList = new ArrayList<Integer>();

	
	static {
		addEntityType();
		entityTypeList.trimToSize();
	}

	
	
	/**
	 * F�gt dem Spiel neue Gegnertypen hinzu.
	 * Je �fter diese hinzugef�gt werden, desto wahrscheinlicher erscheinen sie im Spiel.
	 * Folgende Gegner werden hinzu gef�gt:
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	 private static void  addEntityType__wrappee__Enemies  () {}

	
	
	/**{@feature 1}
	 * Tausendf��ler (1x)
	 */
	private static void addEntityType() {
		entityTypeList.add(IEntity.CENTIPEDE);
		addEntityType__wrappee__Enemies();
	}

	
	
	public static IKIEntity getEnemy() {
		return LASTINSTANCE.enemy;
	}

	
	
	private IKIEntity enemy;

	
	private int countEntity = entityTypeList.size() + 1;

	
	
	/**
	 * Bestimmt zuf�llig einen neuen Gegner.
	 */
	private void createRandomEnemy() {
		if (--countEntity > 0) {
			enemy = newEntity(entityTypeList.get(rand.nextInt(entityTypeList.size())), rand.nextInt(4));
		} else {
			enemy = null;
		}
	}

	
	
	/**
	 * Erstellt einen neuen Gegner des gegebenen Typs.
	 * Folgende Gegner k�nnen erstellt werden:
	 * 
	 * @param type der Gegnertyp
	 * @param route der Richtung, in die sich der Gegner bewegt
	 * @return neue Instanz des Gegener
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	 private IKIEntity  newEntity__wrappee__Enemies  (int type, int route) {
		return null;
	}

	
	
	/**{@feature 1}
	 * Tausendf��ler
	 */
	private IKIEntity newEntity(int type, int route) {
		IKIEntity enemy = newEntity__wrappee__Enemies(type, route);
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

	
	private boolean snakeIsActivated = false;


}
