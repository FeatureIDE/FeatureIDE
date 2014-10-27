package entitys.util;

/**
 * Das Interface aller Entitäten.
 *
 * @author Reimar Schröter
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see IEntityPart
 */
public interface IEntity extends Iterable<IEntityPart> {
	
	/**
     * Arten der Entitäten.
     * 
     * @see IEntity#getType()
     */
	public static final int SNAKE = 0;
	public static final int BUG = 1;
	public static final int SLUG = 2;
	public static final int CENTIPEDE = 3;
	public static final int MOUSE = 4;
	public static final int FLY = 5;

	/**
	 * Gibt den Kopf der Entität zurück.
	 * 
	 * @return der Kopf der Entität
	 * 
	 * @see #getTail()
	 */
	public IEntityPart getHead();
	
	/**
	 * Gibt das letzte Teil der Entität zurück.</br>
	 * Liefert dasselbe Ergebnis wie {@link #getHead()}, wenn die Entität nur aus einem Teil besteht.
	 * 
	 * @return das letzte Teil der Entität
	 * 
	 * @see #getHead()
	 */
	public IEntityPart getTail();
	
	/**
     * Gibt die Art der Entität zurück.
     *
     * @return die Art der Entität
     */
    public int getType();
}
