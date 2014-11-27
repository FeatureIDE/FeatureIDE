package menu;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Image;
import java.util.ArrayList;

import javax.swing.JPanel;

import basics.MainWindow;
import basics.field.Level;
import basics.util.IPanelListener;

/**
 * Hauptmenü des Spiels (grafisch).
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see basics.MainWindow
 */
public class MainMenu extends JPanel implements IPanelListener {
	private static final long serialVersionUID = 1L;
	
	private static final ArrayList<String> menuElements = new ArrayList<String>();
	private static final int numberMenuElements;
	static {
		addMenuElements();
		menuElements.trimToSize();
		numberMenuElements = menuElements.size();
	}
	
	/**
	 * Fügt dem Menü neue Elemente hinzu.
	 */
	/**{@feature 0}
	 * Spiel starten.</br>
	 * Einstellungen.</br>
	 * Anleitung.</br>
	 * Impressum.</br>
	 * Ende.
	 */
	private static void addMenuElements() {
		menuElements.add("Spiel starten");
		menuElements.add("Einstellungen");
		menuElements.add("Anleitung");
		menuElements.add("Impressum");
		menuElements.add("Ende");
	}
	
	private Image backroundImage = null;
	private final MainWindow main;
	
	private int xpos = 0, ypos = 0, width = 0, height = 0, centerPosition = 0, selected = 0, lastElementSize = 0;

	/**
	 * Konstruktor des Hauptmenues.
	 * 
	 * @param main das Hauptfenster des Spiels
	 */
	public MainMenu(MainWindow main) {
		this.main = main;
	}

	public void keyPressed(int keyCode) {
		if (keyCode == 38) {// oben
			selected = (selected + numberMenuElements - 1) % numberMenuElements;
		}
		if (keyCode == 40) {// unten
			selected = (selected + 1) % numberMenuElements;
		}
		if (keyCode == 80 || keyCode == 10) {// bestätigen
			switch (selected) {
			case 0:
				main.startGame();
				break;
			case 1:
				main.startSettings();
				break;
			case 2:
				main.startInstruction();
				break;
			case 3:
				main.impressum();
				break;
			case 4:
				main.exit();
				break;
			default:
				testOtherMenuPoints();
			}
		}
		repaint();
	}
	/**
	 * Führt hinzugefügt Menüpunkte aus. 
	 */
	/**{@feature 0}
	 * Hook method.
	 */
	private void testOtherMenuPoints() {}

	/**
	 * Zeichnet den aktuellen Menüstand.
	 * 
	 * @param g Graphics auf der gemalt werden soll
	 */
	public void paint(Graphics g) {
		if (backroundImage == null || main.getElementSize() != lastElementSize) {
			lastElementSize = main.getElementSize();
			
			final Level mainMenuLevel = new Level(lastElementSize);
			
			int indexX = mainMenuLevel.getMaxX();
			int indexY = mainMenuLevel.getMaxY();
			backroundImage = main.getPainter().paintFrame(mainMenuLevel, null);
			
			width = indexX * lastElementSize;
			height = indexY * lastElementSize;
		}
		
		centerPosition = height >> 1;
		
		g.setColor(Color.BLACK);

		g.fillRect(0, 0, width, height);
		g.drawImage(backroundImage, xpos, ypos + 20, width, height + 20, 0, 0, width, height, null);
		
		g.setColor(Color.RED);

		g.drawLine(0, centerPosition -  2, width, centerPosition -  2);
		g.drawLine(0, centerPosition -  3, width, centerPosition -  3);
		g.drawLine(0, centerPosition + 15, width, centerPosition + 15);
		g.drawLine(0, centerPosition + 16, width, centerPosition + 16);
		
		int index = selected + numberMenuElements - 1;
		g.drawString(menuElements.get(index++ % numberMenuElements), 20, centerPosition - 10);
		g.drawString(menuElements.get(index++ % numberMenuElements), 20, centerPosition + 10);
		g.drawString(menuElements.get(index++ % numberMenuElements), 20, centerPosition + 30);
		
		main.repaint();
	}

}
