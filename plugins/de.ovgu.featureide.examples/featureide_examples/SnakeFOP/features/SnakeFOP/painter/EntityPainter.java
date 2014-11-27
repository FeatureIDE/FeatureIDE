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

/**
 * Zeichnet Entitäten.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 */
public class EntityPainter {

	private static final int bigBildDim = 11;

	private int xPicture;
	private int yPicture;

	private Image entityPictures = null;
	
	private Graphics g = null;

	/**
	 * Erstellt einen neuen Zeichner.
	 * 
	 * @param xPictureI
	 *            Frame Größe in X-Richtung
	 * @param yPictureI
	 *            Frame Größe in Y-Richtung
	 */
	/**{@feature 0}
	 * Das Bild mit den Entitäten wird eingelesen und in Arrays gepeichert.
	 */
	EntityPainter(int xPictureI, int yPictureI) {
		xPicture = xPictureI;
		yPicture = xPictureI;
		
		try {
			entityPictures = ImageIO.read(Painter.class.getResource(MyIO.FILENAME_ENTITIES));
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
	private void paintEnemy(IEntity enemy) {
		paintEntity(enemy);
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
	private int[] getGraphics(IEntity entity) {
		return null;
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
}
