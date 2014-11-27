package basics.field;

import java.io.*;
import java.util.Random;

/**
 * Durch diese Klasse wird das Zugreifen auf ein Feld aus {@link Tile}s ermöglicht.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn 
 * 
 * @version 1.0
 */
public class Level {
	private int tileSize = 9;
	private Tile[][] tileArray; // tileArray in dem alle Tile gespeichert sind
	private int maxX;
	private int maxY;
	
	private Tile snakeStart = null;

	// Hilfsvariablen
	private String readData = null;
	private int dataIndex = -1;

	/**
	 * Erstellt ein neues Field.
	 * 
	 * @param size Größe in der die Tile dargestellt werden sollen
	 */
	public Level(int size) {
		tileSize = size;
		maxX = 23; // / size;
		maxY = 20; // / size;
		
		tileArray = new Tile[maxX][maxY];
		final Random rand = new Random();
		for (int m = 0; m < maxX; m++) {
			for (int n = 0; n < maxY; n++) {
				tileArray[m][n] = new Tile(m * size, n * size, 2, rand.nextInt(4));
			}
		}
		if ((maxX >= 23 && maxY > 7)) {
			int startHeadPositionX = (maxX - 23) / 2;
			// S
			tileArray[startHeadPositionX + 1][1] = new Tile((startHeadPositionX + 1) * size, 1 * size, 60, 1);
			tileArray[startHeadPositionX + 1][2] = new Tile((startHeadPositionX + 1) * size, 2 * size, 60, 2);
			tileArray[startHeadPositionX + 1][3] = new Tile((startHeadPositionX + 1) * size, 3 * size, 60, 3);
			tileArray[startHeadPositionX + 2][1] = new Tile((startHeadPositionX + 2) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 3][1] = new Tile((startHeadPositionX + 3) * size, 1 * size, 60, 1);
			tileArray[startHeadPositionX + 2][3] = new Tile((startHeadPositionX + 2) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 3][3] = new Tile((startHeadPositionX + 3) * size, 3 * size, 60, 3);
			tileArray[startHeadPositionX + 3][4] = new Tile((startHeadPositionX + 3) * size, 4 * size, 60, 0);
			tileArray[startHeadPositionX + 3][5] = new Tile((startHeadPositionX + 3) * size, 5 * size, 60, 1);
			tileArray[startHeadPositionX + 2][5] = new Tile((startHeadPositionX + 2) * size, 5 * size, 60, 2);
			tileArray[startHeadPositionX + 1][5] = new Tile((startHeadPositionX + 1) * size, 5 * size, 60, 3);
			// N
			tileArray[startHeadPositionX + 5][1] = new Tile((startHeadPositionX + 5) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 5][2] = new Tile((startHeadPositionX + 5) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 5][3] = new Tile((startHeadPositionX + 5) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 5][4] = new Tile((startHeadPositionX + 5) * size, 4 * size, 60, 3);
			tileArray[startHeadPositionX + 5][5] = new Tile((startHeadPositionX + 5) * size, 5 * size, 60, 0);
			tileArray[startHeadPositionX + 6][2] = new Tile((startHeadPositionX + 6) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 7][3] = new Tile((startHeadPositionX + 7) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 8][1] = new Tile((startHeadPositionX + 8) * size, 1 * size, 60, 3);
			tileArray[startHeadPositionX + 8][2] = new Tile((startHeadPositionX + 8) * size, 2 * size, 60, 0);
			tileArray[startHeadPositionX + 8][3] = new Tile((startHeadPositionX + 8) * size, 3 * size, 60, 1);
			tileArray[startHeadPositionX + 8][4] = new Tile((startHeadPositionX + 8) * size, 4 * size, 60, 2);
			tileArray[startHeadPositionX + 8][5] = new Tile((startHeadPositionX + 8) * size, 5 * size, 60, 3);
			// A
			tileArray[startHeadPositionX + 10][1] = new Tile((startHeadPositionX + 10) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 10][2] = new Tile((startHeadPositionX + 10) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 10][3] = new Tile((startHeadPositionX + 10) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 10][4] = new Tile((startHeadPositionX + 10) * size, 4 * size, 60, 3);
			tileArray[startHeadPositionX + 10][5] = new Tile((startHeadPositionX + 10) * size, 5 * size, 60, 0);
			tileArray[startHeadPositionX + 11][1] = new Tile((startHeadPositionX + 11) * size, 1 * size, 60, 1);
			tileArray[startHeadPositionX + 11][3] = new Tile((startHeadPositionX + 11) * size, 3 * size,  0, 2);
			tileArray[startHeadPositionX + 12][1] = new Tile((startHeadPositionX + 12) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 12][2] = new Tile((startHeadPositionX + 12) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 12][3] = new Tile((startHeadPositionX + 12) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 12][4] = new Tile((startHeadPositionX + 12) * size, 4 * size, 60, 3);
			tileArray[startHeadPositionX + 12][5] = new Tile((startHeadPositionX + 12) * size, 5 * size, 60, 0);
			// K
			tileArray[startHeadPositionX + 14][1] = new Tile((startHeadPositionX + 14) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 14][2] = new Tile((startHeadPositionX + 14) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 14][3] = new Tile((startHeadPositionX + 14) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 14][4] = new Tile((startHeadPositionX + 14) * size, 4 * size, 60, 3);
			tileArray[startHeadPositionX + 14][5] = new Tile((startHeadPositionX + 14) * size, 5 * size, 60, 0);
			tileArray[startHeadPositionX + 15][3] = new Tile((startHeadPositionX + 15) * size, 3 * size, 60, 0);
			tileArray[startHeadPositionX + 16][2] = new Tile((startHeadPositionX + 16) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 16][4] = new Tile((startHeadPositionX + 16) * size, 4 * size, 60, 2);
			tileArray[startHeadPositionX + 17][1] = new Tile((startHeadPositionX + 17) * size, 1 * size, 60, 3);
			tileArray[startHeadPositionX + 17][5] = new Tile((startHeadPositionX + 17) * size, 5 * size, 60, 0);
			// E
			tileArray[startHeadPositionX + 19][1] = new Tile((startHeadPositionX + 19) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 19][2] = new Tile((startHeadPositionX + 19) * size, 2 * size, 60, 1);
			tileArray[startHeadPositionX + 19][3] = new Tile((startHeadPositionX + 19) * size, 3 * size, 60, 2);
			tileArray[startHeadPositionX + 19][4] = new Tile((startHeadPositionX + 19) * size, 4 * size, 60, 3);
			tileArray[startHeadPositionX + 19][5] = new Tile((startHeadPositionX + 19) * size, 5 * size, 60, 0);
			tileArray[startHeadPositionX + 20][1] = new Tile((startHeadPositionX + 20) * size, 1 * size, 60, 0);
			tileArray[startHeadPositionX + 21][1] = new Tile((startHeadPositionX + 21) * size, 1 * size, 60, 1);
			tileArray[startHeadPositionX + 20][3] = new Tile((startHeadPositionX + 20) * size, 3 * size, 60, 0);
			tileArray[startHeadPositionX + 21][3] = new Tile((startHeadPositionX + 21) * size, 3 * size, 60, 1);
			tileArray[startHeadPositionX + 20][5] = new Tile((startHeadPositionX + 20) * size, 5 * size, 60, 0);
			tileArray[startHeadPositionX + 21][5] = new Tile((startHeadPositionX + 21) * size, 5 * size, 60, 1);
		}
	}

	/**
	 * Es wird ein neues Feld erzeugt, indem eine Karte aus einer Datei geladen
	 * wird.
	 * 
	 * @param path
	 *            Speicherort der Datei wird angegeben, oder eigentliche Karte
	 * @param loadIntern
	 *            gibt an ob die Level intern vom Jar geladen werden sollen
	 */
	public Level(String path, boolean loadIntern) {
		loadField(path, loadIntern);
	}

	/**
	 * Gibt ein boolean[][] zurück in der von jedem Tile die Begehbarkeit
	 * gespeichert sind.
	 * 
	 * @return Array mit den Begehbarkeit-Informationen zu jedem Tile
	 */
	public boolean[][] getAllWalkable() {
		boolean[][] bool = new boolean[maxX][maxY];
		for (int i = 0; i < maxX; i++) {
			for (int l = 0; l < maxY; l++) {
				if (tileArray[i][l].isWalkable()) {
					bool[i][l] = true;
				} else {
					bool[i][l] = false;
				}
			}
		}
		return bool;
	}

	/**
	 * Gibt den die Größe des Feldes in X-Richtung zurück.
	 * 
	 * @return Anzahl der Tile in x-Richtung
	 */
	public int getMaxX() {
		return maxX;
	}

	/**
	 * Gibt den die Größe des Feldes in Y-Richtung zurück.
	 * 
	 * @return Anzahl der Tile in y-Richtung
	 */
	public int getMaxY() {
		return maxY;
	}

	/**
	 * Diese Methode gibt ein Tile aus dem Array zurück, basierend auf den
	 * Indexwerten des Arrays.
	 * 
	 * @param indX
	 *      x-Index des Tile's im Array
	 * @param indY
	 * 		y-Index des Tile's im Array
	 * @return Tile an der angegebenen Position im Array
	 */
	public Tile getTile(int indX, int indY) {
		Tile tmp = tileArray[indX][indY].copy();
		return tmp;
	}

	/**
	 * Gibt die Größe der Tile's im Array zurück.
	 * 
	 * @return int Größe der Tile's im Array
	 */
	public int getTileSize() {
		return tileSize;
	}

	/**
	 * Hier kann erfragt werden ob eine bestimmte Stelle des Feldes begehbar
	 * ist.
	 * 
	 * @param x
	 * 		absolute x-Position des Tile's im Field
	 * @param y
	 * 		absolute y-Position des Tile's im Field
	 * @return boolean Tile begehbar?
	 */
	public boolean getWalkableAbsolutPos(int x, int y) {
		return tileArray[x / tileSize][y / tileSize].isWalkable();
	}

	/**
	 * Gibt die x-Position für den Start der Schlange zurück.
	 * 
	 * @return x-Position für den Startpunkt der Schlange
	 */
	public int getXStartSnake() {
		return getStartSnake().getXPos() + (tileSize / 2);
	}

	/**
	 * Gibt die y-Position für den Start der Schlange zurück.
	 * 
	 * @return y-Position für den Startpunkt der Schlange
	 */
	public int getYStartSnake() {
		return getStartSnake().getYPos() + (tileSize / 2);
	}

	/**
	 * Hier wird gesagt ob die eingebene Position sich auf einer Mittellinie
	 * eines Tile's ist.
	 * 
	 * @param position
	 */
	public boolean isCenterOfTile(int position) {
		if (position % tileSize == 4 * (tileSize / 9)) {
			return true;
		}
		return false;
	}

	public void resizeField(int faktor) {
		tileSize *= faktor;
		for (int i = 0; i < maxX; i++) {
			for (int l = 0; l < maxY; l++) {
				Tile tmp = tileArray[i][l];
				Tile tmpNewTile = tmp.copy();
				tmpNewTile.setSize(tileSize);
				tmpNewTile.setXpos(i * (tileSize));
				tmpNewTile.setYpos(l * (tileSize));
				tileArray[i][l] = tmpNewTile;
			}
		}
	}

	/**
	 * Hier kann an einer bestimmten Stelle des Fields das Tile begehbar oder
	 * nicht begehbar gesetzt werden.
	 * 
	 * @param x
	 *            absolute x-Position des Tile's im Field
	 * @param y
	 *            absolute y-Position des Tile's im Field
	 * @param walkable
	 *            ist das Tile begebar?
	 */
	public void setWalkableAbsolutPos(int x, int y, boolean walkable) {
		tileArray[x / tileSize][y / tileSize].setWalkable(walkable);
	}

	/**
	 * Hier werden die einzelnen infos aus der Karte gesplittet ,diese Methode
	 * wird nur bei dem laden der Karte verwendet.
	 * 
	 * @return String nächste Information aus dem String
	 */
	private String getNextDataInformation() {
		if (readData != null && dataIndex >= 0) {
			final int firstIndex = readData.indexOf('\n', dataIndex);
			final String info;
			if (firstIndex >= 0) {
				info = readData.substring(dataIndex, firstIndex);
				dataIndex = firstIndex + 1;
			} else {
				info = readData.substring(dataIndex, readData.length());
				readData = null;
				dataIndex = -1;
			}
			return info;
		}
		return null;
	}

	/**
	 * Hier bekommt man das Tile von dem aus die Schlange gestartet werden soll.
	 * 
	 * @return Start-Tile der Schlange
	 */
	private Tile getStartSnake() {
		if (snakeStart == null) {
			for (int i = 0; i < maxX; i++) {
				Tile[] tiles = tileArray[i];
				for (int l = 0; l < maxY; l++) {
					Tile tile = tiles[l];
					if (tile.getImgNr() == 0 || tile.getImgNr() == 1) {
						snakeStart = tile;
						break;
					}
				}
			}
		}
		return snakeStart;
	}

	/**
	 * Hier wird die Karte aus einer Datei geladen, und als neues Feld abgelegt.
	 * 
	 * @param path
	 *            Speicherort der Datei
	 * @param loadIntern
	 *            gibt an ob die level intern vom jar geladen werden sollen
	 */
	private void loadField(String path, boolean loadIntern) {
		StringBuilder data = null;
		try {
			InputStream fis = null;
			if (loadIntern) {
				fis = getClass().getResourceAsStream(path);
			} else {
				// FileConnection fc =
				// (FileConnection)Connector.open(path,Connector.READ);
				// fis = fc.openInputStream();
			}
			final int estimatedLength = fis.available();
			if (estimatedLength > 0) {
				data = new StringBuilder(estimatedLength);
			} else {
				data = new StringBuilder();
			}
			int readChar = fis.read();
			while (readChar != -1) {
				data.append((char) readChar);
				readChar = fis.read();
			}
			fis.close();
		} catch (IOException e) {
			System.err.println("Field: Fehler beim laden der Datei "
					+ e.getMessage());
		}
		if (data != null) {
			readData = data.toString();
			dataIndex = 0;
		} else {
			readData = null;
			dataIndex = -1;
		}
		int xIndex = Integer.parseInt(getNextDataInformation());
		int yIndex = Integer.parseInt(getNextDataInformation());
		int size = Integer.parseInt(getNextDataInformation());
		// System.out.println(size);
		maxX = xIndex;
		maxY = yIndex;
		Tile[][] loadedArray = new Tile[xIndex][yIndex];
		for (int i = 0; i < xIndex; i++) {
			for (int l = 0; l < yIndex; l++) {
				Tile tile = new Tile(i * size, l * size,
						Integer.parseInt(getNextDataInformation()),
						Integer.parseInt(getNextDataInformation()));
				tile.setWalkable(getNextDataInformation().charAt(0) == 't');
				loadedArray[i][l] = tile;
			}
		}
		tileArray = loadedArray;
	}
}
