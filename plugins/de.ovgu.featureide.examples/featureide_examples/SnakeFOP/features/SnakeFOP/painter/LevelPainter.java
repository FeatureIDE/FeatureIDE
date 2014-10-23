package painter;

import java.awt.Image;
import java.awt.image.BufferedImage;

import javax.imageio.ImageIO;

import basics.field.Level;
import basics.field.Tile;
import entitys.util.EntityHelpings;

/**
 * Zeichnet ein Level.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 */
public class LevelPainter {
	private final int width;
	private final int height;
	private Image[][] array = new Image[85][4];
	private Image backround = null;
	private Image tileset = null;
	private String root = "/picture/tileset.png";

	/**
	 * Malt das übergebene Field.
	 * 
	 * @param width Breite des zu malenenden Hintergrunds
	 * @param height Länge des zu malenenden Hintergrunds
	 */
	LevelPainter(int width, int height) {
		this.width = width;
		this.height = height;
	}

	/**
	 * Setzt des Hintergrundbild zurück.
	 */
	public void newLevel() {
		backround = null;
	}

	/**
	 * Das übergebene Feld wird als Image gezeichnet.
	 * 
	 * @param level das aktuelle Level
	 * @return das erstellete Image
	 * 
	 */
	public Image paintField(Level level) {
		if (backround == null) {
			backround = new BufferedImage(width, height, BufferedImage.TYPE_INT_ARGB);
			int tilesize = level.getTileSize();
			try {
				tileset = ImageIO.read(Painter.class.getResource(root));
			} catch (Exception e) {
				e.printStackTrace();
			}
			int x = 0;
			for (int i = 0; i < 4; ++i) {
				int y = 0;
				for (int j = 0; j < 85; ++j) {
					BufferedImage tmp = new BufferedImage(tilesize, tilesize, BufferedImage.TYPE_INT_ARGB);
					array[j][i] = tmp;
					tmp.getGraphics().drawImage(tileset, 0, 0, tilesize, tilesize, 
							x, 
							y,
							x + EntityHelpings.TILESIZE, 
							y + EntityHelpings.TILESIZE, null);
					y += EntityHelpings.TILESIZE;
				}
				x += EntityHelpings.TILESIZE;
			}
			int indexX = level.getMaxX();
			int indexY = level.getMaxY();
			for (int m = 0; m < indexX; m++) {
				for (int n = 0; n < indexY; n++) {
					Tile tmp = level.getTile(m, n);
					backround.getGraphics().drawImage(array[tmp.getImgNr()][tmp.getViewNr()], tmp.getXPos(), tmp.getYPos(), null);
				}
			}
		}
		return backround;
	}
}
