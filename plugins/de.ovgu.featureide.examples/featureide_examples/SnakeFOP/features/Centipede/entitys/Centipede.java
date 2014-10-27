package entitys;

import java.util.LinkedList;
import java.util.Queue;

import entitys.util.EntityHelpings;
import entitys.util.IEntityPart;
import entitys.util.IKIEntity;
import basics.field.Level;
import basics.field.GameField;

/**
 * Klasse für eine Tausendfüßlers.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see AEntity
 * @see IKIEntity
 */
public class Centipede extends AEntity implements IKIEntity {

	private int leafsEaten = -1;
	private int deadSince = 0;
	private boolean alive = true;
	/**
	 * Das Blatt, das von einem Tausendfüßler erzeugt wird und von ihm gefressen
	 * werden kann.
	 */
	private EntityPart leaf;
	private int[][] fieldValuation;
	private boolean[][] fieldValuated;
	private boolean[][] fieldWalkableWithoutSnake;

	/**
	 * Creates a new instance of Centipede.
	 * 
	 * @param xPos
	 *            die X Position
	 * @param yPos
	 *            die Y Position
	 * @param route
	 *            die Route des Centipede
	 * @param level
	 *            das Spielfeld
	 */
	public Centipede(int xPos, int yPos, int route, Level level) {
		super(xPos, yPos, route, EntityHelpings.TILESIZE);

		fieldWalkableWithoutSnake = level.getAllWalkable();
		fieldValuation = new int[level.getMaxX()][level.getMaxY()];
		fieldValuated = new boolean[level.getMaxX()][level.getMaxY()];
		newLeaf(level);
		fieldValuate(fieldWalkableWithoutSnake);
		for (int i = 1; i < 5; i++) {
			if (route == 0) {
				yPos += (EntityHelpings.TILESIZE * GameField.getCurFactor());
			} else if (route == 1) {
				xPos -= (EntityHelpings.TILESIZE * GameField.getCurFactor());
			} else if (route == 2) {
				yPos -= (EntityHelpings.TILESIZE * GameField.getCurFactor());
			} else if (route == 3) {
				xPos += (EntityHelpings.TILESIZE * GameField.getCurFactor());
			}
			addPart(new EntityPart(xPos, yPos, route));
		}
	}

	/**
	 * Gibt das vom Tausendfüßlers erzeugte Blatt zurück.
	 * 
	 * @return das aktuelle Blatt
	 */
	public IEntityPart getLeaf() {
		return leaf;
	}

	public int getPoints() {
		if (isAlive()) {
			return Math.max(0, 100 - leafsEaten);
		} else {
			return Math.max(0, 50 - (deadSince / 2));
		}
	}

	public int getType() {
		return IKIEntity.CENTIPEDE;
	}
	
	public boolean isAlive() {
		return alive;
	}
	
	public void kill() {
		alive = false;
		for (EntityPart part : head) {
			part.status = 2;
		}
		head.status = 2;
	}
	
	public void oneStep(Level level) {
		final int stepsize = (EntityHelpings.TILESIZE * GameField.getCurFactor());
		int xIndex = head.xPos / stepsize;
		int yIndex = head.yPos / stepsize;
		
		if (alive) {
			for (EntityPart part : head) {
				part.status = (part.getStatus() + 1) % 2;
			}
			// Leaf essen
			if (EntityHelpings.getDist(head, leaf) == stepsize) {
				if (++leaf.status > 3) {
					newLeaf(level);
					fieldValuate(fieldWalkableWithoutSnake);
				}
			} else {
				// zum Leaf bewegen

				// abstände Festlegen
				int distanceTileStraight = distNextFieldToLeaf(head.getRoute(), xIndex, yIndex, level);
				int distanceTileLeft = distNextFieldToLeaf(head.getRoute() - 1, xIndex, yIndex, level);
				int distanceTileRight = distNextFieldToLeaf(head.getRoute() + 1, xIndex, yIndex, level);

				if (distanceTileLeft <= distanceTileStraight
						&& distanceTileLeft <= distanceTileRight) {
					head.route = (head.route + 3) % 4;
				} else if (distanceTileRight <= distanceTileStraight
						&& distanceTileRight <= distanceTileLeft) {
						head.route = (head.route + 1) % 4;
				}
				if (distanceTileStraight == Integer.MAX_VALUE
						&& distanceTileLeft == Integer.MAX_VALUE
						&& distanceTileRight == Integer.MAX_VALUE) {
					head.route = (head.route + 1) % 4;
				} else {
					moveBody();
					moveHead();
				}
			}
		} else {
			++deadSince;
		}
	}
	
	private int distNextFieldToLeaf(int route, int xIndex, int yIndex,
			Level field) {
		// wieder route anpassen
		if (route == 4) {
			route = 0;
		}
		if (route == -1) {
			route = 3;
		}

		if ((route == 0 && yIndex == 0)
				|| (route == 1 && xIndex >= fieldValuated.length - 1)
				|| (route == 2 && yIndex >= fieldValuated[0].length - 1)
				|| (route == 3 && xIndex == 0)) {
			return Integer.MAX_VALUE;
		}
		if (route == 0) {
			if (field.getWalkableAbsolutPos((xIndex) * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
					(yIndex - 1) * (EntityHelpings.TILESIZE * GameField.getCurFactor()))) {
				return fieldValuation[xIndex][yIndex - 1];
			}
		}
		if (route == 1) {
			if (field.getWalkableAbsolutPos((xIndex + 1) * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
					(yIndex) * (EntityHelpings.TILESIZE * GameField.getCurFactor()))) {
				return fieldValuation[xIndex + 1][yIndex];
			}
		}
		if (route == 2) {
			if (field.getWalkableAbsolutPos((xIndex) * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
					(yIndex + 1) * (EntityHelpings.TILESIZE * GameField.getCurFactor()))) {
				return fieldValuation[xIndex][yIndex + 1];
			}
		}
		if (route == 3) {
			if (field.getWalkableAbsolutPos((xIndex - 1) * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
					(yIndex) * (EntityHelpings.TILESIZE * GameField.getCurFactor()))) {
				return fieldValuation[xIndex - 1][yIndex];
			}
		}

		return Integer.MAX_VALUE;
	}

	private void fieldValuate(boolean[][] fieldWithoutEntity) {
		boolean wayFounded = false;
		boolean start = true;
		// alle Entfernungen werden auf Maximal gesetzt
		// und alle Felder unbewertet
		for (int i = 0; i < fieldValuation.length; i++) {
			for (int j = 0; j < fieldValuation[0].length; j++) {
				fieldValuation[i][j] = Integer.MAX_VALUE;
				fieldValuated[i][j] = false;
			}
		}

		Queue<int[]> queue = new LinkedList<int[]>();
		queue.offer(new int[]{
				leaf.getXPos() / (EntityHelpings.TILESIZE * GameField.getCurFactor()), 
				leaf.getYPos() / (EntityHelpings.TILESIZE * GameField.getCurFactor())});
		fieldValuated[leaf.getXPos() / (EntityHelpings.TILESIZE * GameField.getCurFactor())][leaf.getYPos()
				/ (EntityHelpings.TILESIZE * GameField.getCurFactor())] = true;
		while (!queue.isEmpty() || wayFounded) {
			int[] head = queue.poll();
			// entfernung festlegen
			if (start) {
				start = false;
				fieldValuation[head[0]][head[1]] = 0;
			} else {
				fieldValuation[head[0]][head[1]] = minOfSourrounding(head, fieldWithoutEntity) + (EntityHelpings.TILESIZE * GameField.getCurFactor());
			}

			// Umgebungsfelder in Queue anhängen
			// Feld links vom Start
			if (head[0] > 0) {
				if (fieldValuated[head[0] - 1][head[1]] == false
						&& fieldWithoutEntity[head[0] - 1][head[1]] == true) {
					queue.offer(new int[]{head[0] - 1, head[1]});
					fieldValuated[head[0] - 1][head[1]] = true;
				}
			}
			// Feld oberhalb des Start
			if (head[1] > 0) {
				if (fieldValuated[head[0]][head[1] - 1] == false
						&& fieldWithoutEntity[(head[0])][head[1] - 1] == true) {
					queue.offer(new int[]{head[0], head[1] - 1});
					fieldValuated[head[0]][head[1] - 1] = true;
				}
			}
			// Feld rechts vom Start
			if (head[0] < fieldWithoutEntity.length - 1) {
				if (fieldValuated[head[0] + 1][head[1]] == false
						&& fieldWithoutEntity[(head[0] + 1)][head[1]] == true) {
					queue.offer(new int[]{head[0] + 1, head[1]});
					fieldValuated[head[0] + 1][head[1]] = true;
				}
			}
			// Feld unterhalb des Strat
			if (head[1] < fieldWithoutEntity[0].length - 1) {
				if (fieldValuated[head[0]][head[1] + 1] == false
						&& fieldWithoutEntity[(head[0])][head[1] + 1] == true) {
					queue.offer(new int[]{head[0], head[1] + 1});
					fieldValuated[head[0]][head[1] + 1] = true;
				}
			}

		}
	}

	/**
	 * Gibt das Minimum der Bewertungen in der Umgebung des Elementes zurück. Es
	 * können auch Elemente am rand eingegeben werden.
	 * 
	 * @param element X/Y-Pos
	 * 
	 * @param field Gibt an, wleches Feld begehbar ist.
	 * 
	 * @return Minimum der Umgebung
	 */
	private int minOfSourrounding(int[] element, boolean[][] field) {
		// Element oben,links
		if (element[0] == 0 && element[1] == 0) {
			return Math.min(fieldValuation[0][1], fieldValuation[1][0]);
		}
		// Element unten,links
		if (element[0] == 0
				&& element[1] == field[0].length - 1) {
			return Math.min(fieldValuation[0][field[0].length - 2],
					fieldValuation[1][field[0].length - 1]);
		}
		// Element unten,rechts
		if (element[0] == field.length - 1
				&& element[1] == field[0].length - 1) {
			return Math.min(
					fieldValuation[field.length - 1][field[0].length - 2],
					fieldValuation[field.length - 2][field[0].length - 1]);
		}
		// Element oben,rechts
		if (element[0] == field.length - 1 && element[1] == 0) {
			return Math.min(fieldValuation[field.length - 1][1],
					fieldValuation[field.length - 2][0]);
		}
		// links Rand
		if (element[0] == 0) {
			int hilf = Math.min(fieldValuation[0][element[1] + 1],
					fieldValuation[0][element[1] - 1]);
			return Math.min(hilf, fieldValuation[1][element[1]]);
		}
		// oben Rand
		if (element[1] == 0) {
			int hilf = Math.min(fieldValuation[element[0] + 1][0],
					fieldValuation[element[0] - 1][0]);
			return Math.min(hilf, fieldValuation[element[0]][1]);
		}
		// rechts Rand
		if (element[0] == field.length - 1) {
			int hilf = Math
					.min(fieldValuation[element[0]][element[1] - 1], fieldValuation[element[0]][element[1] + 1]);
			return Math
					.min(hilf, fieldValuation[element[0] - 1][element[1]]);
		}
		// unten Rand
		if (element[1] == field[0].length - 1) {
			int hilf = Math
					.min(fieldValuation[element[0] - 1][element[1]],
							fieldValuation[element[0] + 1][element[1]]);
			return Math
					.min(hilf, fieldValuation[element[0]][element[1] - 1]);
		}
		// Element nicht am Rand vom Feld
		return Math
				.min(Math.min(fieldValuation[element[0] - 1][element[1]],
						fieldValuation[element[0] + 1][element[1]]),
						Math.min(fieldValuation[element[0]][element[1] - 1], fieldValuation[element[0]][element[1] + 1]));
	}

	/**
	 * Erzeugt ein neues Blatt.
	 */
	private void newLeaf(Level field) {
		int[] position = EntityHelpings.walkableRandomFieldIndex();
		leafsEaten++;
		leaf = new EntityPart(
				position[0] * (EntityHelpings.TILESIZE * GameField.getCurFactor()) + (4 * GameField.getCurFactor()), 
				position[1] * (EntityHelpings.TILESIZE * GameField.getCurFactor()) + (4 * GameField.getCurFactor()), -1);
	}
}
