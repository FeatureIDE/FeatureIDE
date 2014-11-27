package entitys.util;

import basics.field.Level;

/**
 * Das Interface für eine nicht spielbare Entität.
 * 
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see IEntity
 */
public interface IKIEntity extends IEntity {
	/**
	 * Lässt die Entität einen Zug machen.
	 * 
	 * @param level das aktuelle Level
	 */
	public void oneStep(Level level);
	
	/**
	 * Berechnet die Punkte für das Essen eines Teils der Entität.
	 * 
	 * @return die Punkte
	 */
	public int getPoints();
	
	/**
	 * Tötet die Entität.
	 * 
	 * @see #isAlive()
	 */
	public void kill();
	
	/**
	 * Gibt zurück, ob die Entität noch am Leben ist.
	 * 
	 * @return
	 * 	{@code true} falls die Enität lebt,</br>
	 * 	{@code false} falls nicht.
	 * 
	 * @see #kill()
	 */
	public boolean isAlive();
}
