package painter;

import java.awt.Image;

import javax.imageio.ImageIO;

import menu.MyIO;
import basics.field.GameField;
import entitys.Centipede;
import entitys.util.EntityHelpings;

public class EntityPainter {
	
	private static final int smallBildDim = 9;
	private Image entityPictures9 = null;

	// Tausend Image Zeilen
	private int[] centiParts = {8, 0, 3, 1, 4, 6, 7, 2, 5, 9};
	private int[] centiRoute = {0,2,0,3,0,1,3,0,0,1,2,0,1,0,2,3};
	
	/**{@feature 0}
	 * Das Bild mit den Tausendfüssler wird eingelesen und in einem array gepeichert.
	 */
	EntityPainter(int xPictureI, int yPictureI) {
		try {
			entityPictures9 = ImageIO.read(Painter.class.getResource(MyIO.FILENAME_ENTITIES9));
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	/**{@feature 0}
	 * Zeichnet einen Tausendfüßler.
	 */
	private void paintEnemy(IEntity enemy) {
		if (enemy.getType() == IEntity.CENTIPEDE) {
			paintTausend((Centipede) enemy);
		} else {
			original(enemy);
		}
	}
	
	/**{@feature 1}
	 * Gibt die Texturen eines Tausendfüßler zurück.
	 */
	private int[] getGraphics(IEntity entity) {
		if (entity.getType() == IEntity.CENTIPEDE) {
			return centiParts;
		} else {
			return original(entity);
		}
	}
	
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
