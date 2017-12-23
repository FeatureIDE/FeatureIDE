package painter; 

import java.awt.Graphics; 

import java.awt.Image; 
import java.awt.image.BufferedImage; 

import javax.imageio.ImageIO; 

import menu.MyIO; 
import basics.field.GameField; 
import entitys.Snake; 
import entitys.util.EntityHelpings; 
import entitys.util.IEntity; 
import entitys.util.IEntityPart; 
import entitys.Centipede; 

public   class  EntityPainter {
	

	private static final int bigBildDim = 11;

	

	private int xPicture;

	
	private int yPicture;

	

	private Image entityPictures = null;

	
	
	private Graphics g = null;

	
	
	/**{@feature 0}
	 * Das Bild mit den Tausendfüssler wird eingelesen und in einem array gepeichert.
	 */
	EntityPainter  (int xPictureI, int yPictureI) {
		xPicture = xPictureI;
		yPicture = xPictureI;
		
		try {
			entityPictures = ImageIO.read(Painter.class.getResource(MyIO.FILENAME_ENTITIES));
		} catch (Exception e) {
			e.printStackTrace();
		}
	
		try {
			entityPictures9 = ImageIO.read(Painter.class.getResource(MyIO.FILENAME_ENTITIES9));
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	

	// -------------------------------------------------------------------------------------------------------------------------------

	/**
	 * Hier werden alle übergebenen Entitys auf das Hintergrundbild gezeichnet.
	 * 
	 * @param backround
	 * 		das Hintergrundbild
	 * @param entities
	 * 		das Array der zu zeichnenden Entitys
	 * 
	 */
	public Image paintEntitys(Image backround, IEntity[] entities) {
		if (entities == null) {
			return backround;
		}
		BufferedImage frame = new BufferedImage(xPicture, yPicture, BufferedImage.TYPE_INT_ARGB);
		g = frame.getGraphics();
		g.drawImage(backround, 0, 0, null);
		
		Snake snake = (Snake) entities[0];
		boolean snakeAlreadyMoved = snake.alreadyMoved();
		
		if (!snakeAlreadyMoved) {
			paintSnake(snake);
		}
		if (entities[1] != null) {
			paintEnemy(entities[1]);
		}
		if (snakeAlreadyMoved) {
			paintSnake(snake);
		}
//		if (entities[1] != null && entities[1].getType() == IEntity.EntityType.FLY) {
//			Fly fl = (Fly) entities[1];
//			if (fl.isFlying()) {
//				paintEntity(entities[1]);
//			}
//		}
		return frame;
	}

	
	
	/**
	 * Zeichnet einen Gegner.
	 * 
	 * @param enemy der zu zeichnende Gegner
	 */
	/**{@feature 0}
	 * Zeichnet alle eingliedrigen Gegner.
	 */
	 private void  paintEnemy__wrappee__SnakeFOP  (IEntity enemy) {
		paintEntity(enemy);
	}

	
	
	/**{@feature 0}
	 * Zeichnet einen Tausendfüßler.
	 */
	private void paintEnemy(IEntity enemy) {
		if (enemy.getType() == IEntity.CENTIPEDE) {
			paintTausend((Centipede) enemy);
		} else {
			paintEnemy__wrappee__SnakeFOP(enemy);
		}
	}

	

	private void bigPicturePaint(int xPosEntityPicture,	int yPosEntityPicture, int xPosField, int yPosField) {
		g.drawImage(entityPictures, xPosField - (5 * GameField.getCurFactor()), yPosField - (5 * GameField.getCurFactor()),
				2 + xPosField + (EntityHelpings.TILESIZE - 5) * GameField.getCurFactor(),
				2 + yPosField + (EntityHelpings.TILESIZE - 5) * GameField.getCurFactor(), //size 
				xPosEntityPicture * bigBildDim,
				yPosEntityPicture * bigBildDim,
				xPosEntityPicture * bigBildDim + bigBildDim,
				yPosEntityPicture * bigBildDim + bigBildDim, null);
	}

	
	
	/**
	 * Gibt die Texturen einer Entität zurück.
	 * 
	 * @param entity die Entität
	 * 
	 * @return alle Texturen in einem Array
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	 private int[]  getGraphics__wrappee__SnakeFOP  (IEntity entity) {
		return null;
	}

	
	
	/**{@feature 1}
	 * Gibt die Texturen eines Tausendfüßler zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.CENTIPEDE) {
			return centiParts;
		} else {
			return getGraphics__wrappee__SnakeFOP(entity);
		}
	}

	

	private void paintEntity(IEntity entity) {
		int[] graphics = getGraphics(entity);
		for (IEntityPart iEntityPart : entity) {
			bigPicturePaint(
					iEntityPart.getRoute(),
					graphics[iEntityPart.getStatus()],
					iEntityPart.getXPos(),
					iEntityPart.getYPos());
		}
	}

	

	// Snake Image Zeilen
	private int snakeHead = 0;

	
	private int snakeMiddle = 1;

	
	private int snakeTail = 3;

	
	
	private void paintSnake(Snake snake) {
		if (!snake.alreadyMoved()) {
			bigPicturePaint(2, snakeMiddle, snake.getHead().getXPos(),
					snake.getHead().getYPos());
		} else {
			for (IEntityPart snakePart : snake) {
				if (snakePart == snake.getHead()) {
					bigPicturePaint(snakePart.getRoute(),
							snakeHead, snakePart.getXPos(),
							snakePart.getYPos());
				} else if (snakePart == snake.getTail()) {
					bigPicturePaint(snakePart.getRoute(),
							snakeTail, snakePart.getXPos(),
							snakePart.getYPos());
				} else {
					int x = snakePart.getStatus() >> 2;
					int y = snakePart.getStatus() % 4;
					bigPicturePaint(y,
							x, snakePart.getXPos(),
							snakePart.getYPos());
				}
			}
		}
	}

	
	
	private static final int smallBildDim = 9;

	
	private Image entityPictures9 = null;

	

	// Tausend Image Zeilen
	private int[] centiParts = {8, 0, 3, 1, 4, 6, 7, 2, 5, 9};

	
	private int[] centiRoute = {0,2,0,3,0,1,3,0,0,1,2,0,1,0,2,3};

	
	
	private void paintTausend(Centipede centi) {
		int dist = (EntityHelpings.TILESIZE * GameField.getCurFactor()) / 2;
		IEntityPart leaf = centi.getLeaf();
		smallPicturePaint(leaf.getStatus(), centiParts[9], 
				leaf.getXPos() - dist, leaf.getYPos() - dist);

		// Tausendfüßler zeichnen
		// Kopf zeichnen
		int count = 0;
		IEntityPart last = null;
		for (IEntityPart iEntityPart : centi) {
			if (iEntityPart.isAlive()) {
				if (!centi.isAlive()) {
					smallPicturePaint(0, centiParts[0], iEntityPart.getXPos(), iEntityPart.getYPos());
				} else {
					if (count == 0) {
						smallPicturePaint(iEntityPart.getRoute(), centiParts[1 + (iEntityPart.getStatus() % 2)], 
								iEntityPart.getXPos(), iEntityPart.getYPos());
					} else if (count >= 2) {
						System.out.println();
						final int x = centiRoute[(4 * last.getRoute()) + iEntityPart.getRoute()];
						final int y; // = 5;
						if (last.getRoute() == iEntityPart.getRoute()) {
							y = 3 + (iEntityPart.getStatus() % 2);
						} else {
							final int status = (iEntityPart.getStatus() + ((x < 2) ? 0 : 1)) % 2;
							y = 5 + status;
						}
						smallPicturePaint(x, centiParts[y], last.getXPos(), last.getYPos());
					}
				}
			}
			++count;
			last = iEntityPart;
		}
		smallPicturePaint(last.getRoute(), centiParts[7 + (last.getStatus() % 2)], 
				last.getXPos(), last.getYPos());
	}

	
	
	private void smallPicturePaint(int xPosEntityPicture, int yPosEntityPicture, int xPosField, int yPosField) {
		g.drawImage(entityPictures9, xPosField - (5 * GameField.getCurFactor()), yPosField - (5 * GameField.getCurFactor()),
				xPosField + (EntityHelpings.TILESIZE - 5) * GameField.getCurFactor(),
				yPosField + (EntityHelpings.TILESIZE - 5) * GameField.getCurFactor(), 
				xPosEntityPicture * smallBildDim,
				yPosEntityPicture * smallBildDim,
				xPosEntityPicture * smallBildDim + smallBildDim, 
				yPosEntityPicture * smallBildDim + smallBildDim, null);
	}


}
