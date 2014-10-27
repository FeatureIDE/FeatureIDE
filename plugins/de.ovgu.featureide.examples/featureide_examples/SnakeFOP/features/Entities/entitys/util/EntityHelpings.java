package entitys.util;

import java.util.Random;

import basics.field.GameField;
import basics.field.Level;

/**
 * Diese Klasse stellt hilfreiche Methoden für die Entitys zur Verfügung.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 */
public abstract class EntityHelpings {
	/**
	 * Größe eines Tiles in Pixeln.</br>
	 * Der Standardwert ist {@value}.
	 */
	public static final int TILESIZE = 9;
	
	private static final Random rand = new Random();
	
	/**
	 * Berechnet die Distanz zwischen zwei Entitätsteilen.
	 * 
	 * @param entityPart1 ein Teilstück einer Entität
	 * @param entityPart2 ein weiteres Teilstück einer Entität
	 * 
	 * @return der Abstand in Pixeln
	 */
	public static int getDist(IEntityPart entityPart1, IEntityPart entityPart2) {
		final int dx = entityPart1.getXPos() - entityPart2.getXPos();
		final int dy = entityPart1.getYPos() - entityPart2.getYPos();
		return (int) Math.floor(Math.sqrt(dx * dx + dy * dy));
	}
	
	/**
	 * Gibt ein Zufallsfeld was begehbar ist in eime Field zurüch xPos,yPos.
	 * 
	 * @return ein begehbares Tile
	 */
	public static int[] walkableRandomFieldIndex() {
		Level level = GameField.getCurLevel();
		int[] back = new int[2];
		do {
			back[0] = rand.nextInt(level.getMaxX() - 1);
			back[1] = rand.nextInt(level.getMaxY() - 1);
		} while (!level.getWalkableAbsolutPos(
				back[0] * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
				back[1] * (EntityHelpings.TILESIZE * GameField.getCurFactor())));
		return back;
	}

	/**
	 * Gibt die Startposition der Mouse zurück.
	 * 
	 * @param route
	 *            die Richtung der Mouse
	 * @return ein Array mit x und y Position
	 */
	public static int[] mousePos(int route) {
		for (int i = 0; i < 20; i++) {
			int[] position = walkableRandomFieldIndex();
			switch (route) {
			case 0: 
				if (position[1] < GameField.getCurLevel().getMaxY() - 2) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] + 1)
									* (TILESIZE * GameField.getCurFactor()))) {
						return position;
					}
				}
				break;
			case 1: 
				if (position[0] >= 1) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] - 1)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
						return position;
					}
				}
				break;
			case 2:
				if (position[1] >= 1) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] - 1)
									* (TILESIZE * GameField.getCurFactor()))) {
						return position;
					}
				}
				break;
			case 3:
				if (position[0] < GameField.getCurLevel().getMaxX() - 2) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] + 1)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
						return position;
					}
				}
			}
		}
		return null;
	}

	/**
	 * Gibt die Startposition des Centipede zurück.
	 * 
	 * @param route
	 *            die Richtung des Centipede
	 * @return ein Array mit x und y Position
	 */

	public static int[] CentipedePos(int route, int rek) {
		for (int i = 0; i < 20; i++) {
			int[] position = walkableRandomFieldIndexCenti(route);
			switch (route) {
			case 0:
				if (position[1] < GameField.getCurLevel().getMaxY() - 5) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] + 1)
									* (TILESIZE * GameField.getCurFactor()))) {
						if (GameField.getCurLevel().getWalkableAbsolutPos((position[0])
								* (TILESIZE * GameField.getCurFactor()), (position[1] + 2) * (TILESIZE * GameField.getCurFactor()))
								&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
										* (TILESIZE * GameField.getCurFactor()), (position[1] + 3)
										* (TILESIZE * GameField.getCurFactor()))) {
							if (GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] + 4)
									* (TILESIZE * GameField.getCurFactor()))) {
								return position;
							}
						}
					}
				}
				break;
			case 1:
				if (position[0] >= 4) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] - 1)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
						if (GameField.getCurLevel().getWalkableAbsolutPos((position[0] - 2)
								* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))
								&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] - 3)
										* (TILESIZE * GameField.getCurFactor()), (position[1])
										* (TILESIZE * GameField.getCurFactor()))) {
							if (GameField.getCurLevel().getWalkableAbsolutPos((position[0] - 4)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
								return position;
							}
						}
					}
				}
				break;
			case 2:
				if (position[1] >= 4) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] - 1)
									* (TILESIZE * GameField.getCurFactor()))) {
						if (GameField.getCurLevel().getWalkableAbsolutPos((position[0])
								* (TILESIZE * GameField.getCurFactor()), (position[1] - 2) * (TILESIZE * GameField.getCurFactor()))
								&& GameField.getCurLevel().getWalkableAbsolutPos((position[0])
										* (TILESIZE * GameField.getCurFactor()), (position[1] - 3)
										* (TILESIZE * GameField.getCurFactor()))) {
							if (GameField.getCurLevel().getWalkableAbsolutPos((position[0])
									* (TILESIZE * GameField.getCurFactor()), (position[1] - 4)
									* (TILESIZE * GameField.getCurFactor()))) {
								return position;
							}
						}
					}
				}
				break;
			case 3:
				if (position[0] < GameField.getCurLevel().getMaxX() - 5) {
					if (GameField.getCurLevel().getWalkableAbsolutPos((position[0]) * (TILESIZE * GameField.getCurFactor()),
							(position[1]) * (TILESIZE * GameField.getCurFactor()))
							&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] + 1)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
						if (GameField.getCurLevel().getWalkableAbsolutPos((position[0] + 2)
								* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))
								&& GameField.getCurLevel().getWalkableAbsolutPos((position[0] + 3)
										* (TILESIZE * GameField.getCurFactor()), (position[1])
										* (TILESIZE * GameField.getCurFactor()))) {
							if (GameField.getCurLevel().getWalkableAbsolutPos((position[0] + 4)
									* (TILESIZE * GameField.getCurFactor()), (position[1]) * (TILESIZE * GameField.getCurFactor()))) {
								return position;
							}
						}
					}
				}
			}
		}
		return null;
	}

	/**
	 * Gibt ein Zufallsfeld was begehbar ist und für den Tausendfüßler möglich
	 * ist in eime Field zurüch xPos,yPos.
	 * 
	 * @param route
	 *            die Richtung des Tausendfüßlers
	 * @return Array mit x und y Position
	 */
	public static int[] walkableRandomFieldIndexCenti(int route) {
		int[] back = new int[2];
		switch (route) {
		case 0:
			back[0] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxX() - 1));
			back[1] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxY() - 5));
			if (!GameField.getCurLevel().getWalkableAbsolutPos(back[0] * (TILESIZE * GameField.getCurFactor()), back[1]
					* (TILESIZE * GameField.getCurFactor()))) {
				back = walkableRandomFieldIndexCenti(route);
			}
			break;
		case 1:
			back[0] = 4 + Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxX() - 5));
			back[1] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxY() - 1));
			if (!GameField.getCurLevel().getWalkableAbsolutPos(back[0] * (TILESIZE * GameField.getCurFactor()), back[1]
					* (TILESIZE * GameField.getCurFactor()))) {
				back = walkableRandomFieldIndexCenti(route);
			}
			break;
		case 2:
			back[0] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxX() - 1));
			back[1] = 4 + Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxY() - 5));
			if (!GameField.getCurLevel().getWalkableAbsolutPos(back[0] * (TILESIZE * GameField.getCurFactor()), back[1]
					* (TILESIZE * GameField.getCurFactor()))) {
				back = walkableRandomFieldIndexCenti(route);
			}
			break;
		case 3:
			back[0] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxX() - 5));
			back[1] = Math.abs(rand.nextInt() % (GameField.getCurLevel().getMaxY() - 1));
			if (!GameField.getCurLevel().getWalkableAbsolutPos(back[0] * (TILESIZE * GameField.getCurFactor()), back[1]
					* (TILESIZE * GameField.getCurFactor()))) {
				back = walkableRandomFieldIndexCenti(route);
			}
		}
		return back;
	}
}
