package basics.field;

/**
 * Eine Kachel des Spielfeldes.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @see basics.field.Level
 */
public class Tile {
	private int xpos, ypos, size = 0;
	private final int imgNr, viewNr;
	private boolean walkable = true;

	/**
	 * Konstruktor für ein Tile alle benötigten Informationen um ein Tile
	 * darzustelln, werden übergeben.
	 * 
	 * @param xpos x-Position des Tile
	 * @param ypos y-Position des Tile
	 * @param imgNr Bildnummer die dargestellt werden soll
	 * @param viewNr die genaue Darstellungsart des Bildes
	 */
	public Tile(int xpos, int ypos, int imgNr, int viewNr) {
		this.xpos = xpos;
		this.ypos = ypos;
		this.imgNr = imgNr;
		this.viewNr = viewNr;
	}

	/**
	 * Kopiert die Instanz der Kachel.
	 * 
	 * @return eine neue Instanz mit den sleben Attributen
	 */
	public Tile copy() {
		Tile tmp = new Tile(xpos, ypos,imgNr, viewNr);
		tmp.setSize(size);
		tmp.setWalkable(walkable);
		return tmp;
	}

	/**
	 * Gibt die Image Nummer zurück (legt Bild fest).
	 * 
	 * @return Image-Nummer
	 */
	public int getImgNr() {
		return imgNr;
	}

	/**
	 * Gibt an, welche Ansicht das Image haben soll (mehrere Varianten bei z.B.
	 * Stein).
	 * 
	 * @return gibt das genaue Image an
	 */
	public int getViewNr() {
		return viewNr;
	}

	/**
	 * Gibt die x-Position des Tile zurück.
	 * 
	 * @return x-Position
	 * 
	 */
	public int getXPos() {
		return xpos;
	}

	/**
	 * Gibt die Y-Position des Tile zurück.
	 * 
	 * @return Y-Position
	 * 
	 */
	public int getYPos() {
		return ypos;
	}

	/**
	 * Gibt {@code true} zurück wenn das Tile begehbar ist.
	 * 
	 * @return Begehbarkeit
	 * 
	 */
	public boolean isWalkable() {
		return walkable;
	}

	/**
	 * Setzt die Größe des Tile.
	 * 
	 * @param size neue Größe des Tile
	 */
	public void setSize(int size) {
		this.size = size;
	}

	/**
	 * Setzt die Begehbarkeit eines Tile.
	 * 
	 * @param walk
	 * 		bei Begehbarkeit - {@code true}
	 * 
	 */
	public void setWalkable(boolean walk) {
		walkable = walk;
	}

	/**
	 * @param xpos the xpos to set
	 */
	public void setXpos(int xpos) {
		this.xpos = xpos;
	}

	/**
	 * @param ypos the ypos to set
	 */
	public void setYpos(int ypos) {
		this.ypos = ypos;
	}
}
