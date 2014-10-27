package basics.util;

import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;

/**
 * Wrapper-Klasse für das {@link IPanelListener}-Interface.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see KeyListener
 */
public class MyKeyListener implements KeyListener {
	private IPanelListener listener = null;

	/**
	 * Ändert das aktuelle {@link IPanelListener}-Objekt.
	 * 
	 * @param listener der neue PanelListener
	 */
	public void setListener(IPanelListener listener) {
		this.listener = listener;
	}
	
	public void keyPressed(KeyEvent event) {
		listener.keyPressed(event.getKeyCode());
	}
	
	public void keyReleased(KeyEvent event) {}
	public void keyTyped(KeyEvent event) {}
}
