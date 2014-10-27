package basics.util;

/**
 * Listener für Tastatureingaben.
 * 
 * @author Alexander Grebhahn
 * @author Reimar Schröter
 * 
 * @version 1.0
 * 
 * @see basics.field.GameField
 * @see menu.MainMenu
 */
public interface IPanelListener {
	/**
	 * Behandelt gedrückte Tasten.
	 * 
	 * @param keyCode der Code der gedrückten Taste
	 */
	public void keyPressed(int keyCode);
}
