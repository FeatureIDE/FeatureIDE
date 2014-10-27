package entitys.util;

/**
 * Das Interface eines Teilstücks einer Entität.
 * 
 * @author Reimar Schröter,
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see IEntity
 */
public interface IEntityPart {
	/**
	 * Tötet das Teilstück.
	 * 
	 * @see #isAlive()
	 */
	public void eat();

	/**
	 * Die Richtung gibt an, wohin sich das Teilstück bewegt.
	 * 
	 * @return die Richtung des Teilstücks
	 */
	public int getRoute();
	
	/**
	 * Der Status dient zur Darstellung der Teilstücke. 
	 * 
	 * @return der Status des Teilstücks
	 */
	public int getStatus();

	/**
	 * 
	 * @return die X-Position des Teilstücks
	 * 
	 * @see #getYPos()
	 */
	public int getXPos();

	/**
	 * 
	 * @return die Y-Position des Teilstücks
	 * 
	 * @see #getXPos()
	 */
	public int getYPos();
	
	/**
	 * Gibt an, ob das Teilstück der Entität lebendig ist.
	 * 
	 * @return
	 * 	{@code true} falls das Teilstück lebt,</br>
	 * 	{@code false} falls nicht.
	 * 
	 * @see #eat()
	 */
	public boolean isAlive();
}
