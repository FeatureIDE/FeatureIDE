package entitys;

import java.util.LinkedList; 
import java.util.Queue; 

import basics.field.GameField; 
import entitys.util.IEntityPart; 
import entitys.util.IKIEntity; 

public class Snake extends AEntity {
	
	private final int[][] fieldValuation;
	private final boolean[][] fieldValuated;
	private int enemyX;
	private int enemyY;
	
	/**{@feature 0}
	 * Initialisiert Wegfindunsvariablen.
	 */
	public Snake(int xPosbeiStart, int yPosbeiStart, int AnzahlderMittelteilebeimStart) {
		fieldValuation = new int[GameField.getCurLevel().getMaxX()][GameField.getCurLevel().getMaxY()];
		fieldValuated = new boolean[GameField.getCurLevel().getMaxX()][GameField.getCurLevel().getMaxY()];
	}
	
	/**{@feature 1}
	 * Bestimmt die Richtung der Schlange automatisch.
	 */
	public void oneStep(Level field, int countEntity) {
		thinkKI(field);
		original(field, countEntity);
	}
	
	private void thinkKI(Level field) {
		IKIEntity enemy = GameField.getEnemy();
		boolean dead = true;
		if (enemy != null) {
			for (IEntityPart iEntityPart : enemy) {
				if (iEntityPart.isAlive()) {
					enemyX = iEntityPart.getXPos();
					enemyY = iEntityPart.getYPos();
					dead = false;
					break;
				}
			}
		}
		if (dead) {
			enemyX = field.getXStartSnake();
			enemyY = field.getYStartSnake();
		}
		
		fieldValuate(field.getAllWalkable());
		
		if (head.route == -1) {
			head.route = 0;
		}
		
		int xIndex = head.xPos / (EntityHelpings.TILESIZE * GameField.getCurFactor());
		int yIndex = head.yPos / (EntityHelpings.TILESIZE * GameField.getCurFactor());
		
		int distanceTileStraight = distNextFieldToLeaf(head.getRoute(), xIndex, yIndex, field);
		int distanceTileLeft = distNextFieldToLeaf(head.getRoute() - 1, xIndex, yIndex, field);
		int distanceTileRight = distNextFieldToLeaf(head.getRoute() + 1, xIndex, yIndex, field);
		
		if (distanceTileLeft < distanceTileStraight && distanceTileLeft < distanceTileRight) {
			head.route = (head.route + 3) % 4;;
		} else if (distanceTileRight < distanceTileStraight && distanceTileRight < distanceTileLeft) {
			head.route = (head.route + 1) % 4;
		}
	}

	private int distNextFieldToLeaf(int route, int xIndex, int yIndex,
			Level field) {
		// wieder route anpassen
		if (route == 4) {
			route = 0;
		} else if (route == -1) {
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
			if (field.getWalkableAbsolutPos(
					(xIndex) * (EntityHelpings.TILESIZE * GameField.getCurFactor()),
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
				enemyX / (EntityHelpings.TILESIZE * GameField.getCurFactor()), 
				enemyY / (EntityHelpings.TILESIZE * GameField.getCurFactor())});
		fieldValuated[enemyX / (EntityHelpings.TILESIZE * GameField.getCurFactor())]
					 [enemyY / (EntityHelpings.TILESIZE * GameField.getCurFactor())] = true;
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
	 * können auch Elemente am Rand eingegeben werden.
	 * 
	 * @param element X/Y-Pos
	 * 
	 * @param field Gibt an, welches Feld betreten werden kann.
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

}
