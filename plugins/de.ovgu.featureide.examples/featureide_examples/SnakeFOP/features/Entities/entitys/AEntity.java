package entitys;

import java.util.Iterator;
import java.util.Random;

import basics.field.Level;
import basics.field.GameField;
import entitys.util.EntityHelpings;
import entitys.util.IEntity;
import entitys.util.IEntityPart;

/**
 * Die Basis Klasse für alle Entitäten.
 *
 * @author Reimar Schröter,
 * @author Alexander Grebhahn
 * 
 * @version 1.0
 * 
 * @see IEntity
 * @see EntityPart
 */
public abstract class AEntity implements IEntity {
	
	/**
	 * Die Klasse für alle Teile einer Entität.
	 * 
	 * @see IEntityPart
	 */
	protected static class EntityPart implements IEntityPart, Iterable<EntityPart> {
		/**
		 * @see #getXPos()
		 */
		protected int xPos;
		/**
		 * @see #getYPos()
		 */
		protected int yPos;
		/**
		 * @see #getRoute()
		 */
		protected int route;
		/**
		 * @see #getStatus()
		 */
		protected int status = 0;
		/**
		 * @see #isAlive()
		 */
		protected boolean isAlive = true;
		
		/**
		 * Das nächste Teilstück der Entität.
		 */
		protected EntityPart next;

		/**
		 * Erstellt ein neues Teilstück einer Entität.
		 * 
		 * @param xPos die X-Position des Teilstücks
		 * @param yPos die Y-Position des Teilstücks
		 * @param route die Bewegungsrichtung
		 */
		public EntityPart(int xPos, int yPos, int route) {
			this.xPos = xPos;
			this.yPos = yPos;
			this.route = route;
		}
		
		public void eat() {
			isAlive = false;
		}
		
		public int getRoute() {
			return route;
		}
		
		public final int getStatus() {
			return status;
		}
		
	    public int getXPos() {
	        return xPos;
	    }
	    
	    public int getYPos() {
	        return yPos;
	    }
	    
		public boolean isAlive() {
			return isAlive;
		}
		
		public Iterator<EntityPart> iterator() {
			return new Iterator<EntityPart>() {
				private EntityPart cur = EntityPart.this;
				
				public boolean hasNext() {
					return cur != null;
				}
				
				public EntityPart next() {
					final EntityPart ret = cur;
					cur = cur.next;
					return ret;
				}
				
				/**
				 * Die Funktion ist nicht implementiert.
				 */
				public void remove() {}
			};
		}
	}
	
	/**
	 * Konstanten für das Ändern der Bewegungsrichtung, falls die Entität auf ein Hindernis trifft. 
	 */
	protected static final int[] routeChange = {2,1,2};
	
	/**
	 * Eigenes {@link Random}-Objekt für die Erzeugung von Zufallswerten.
	 */
	protected static final Random rand = new Random();
	
	protected EntityPart head;
	protected EntityPart tail;
	
	private final int stepsize;
	
	/**
	 * Erstellt eine neue Entität.
	 * 
	 * @param xPos die X-Position des Kopfs
	 * @param yPos die Y-Position des Kopfs
	 * @param route die Bewegungsrichtung am Anfang
	 * @param stepsize die Schrittweite der Entität
	 */
	public AEntity(int xPos, int yPos, int route, int stepsize) {
		this.stepsize = stepsize * GameField.getCurFactor();
		this.head = new EntityPart(xPos, yPos, route);
		this.tail = head;
	}
	
	public final IEntityPart getHead() {
		return head;
	}
	
	public final IEntityPart getTail() {
		return tail;
	}
	
	public final Iterator<IEntityPart> iterator() {
		return new Iterator<IEntityPart>() {
			private EntityPart next = head;
			
			public boolean hasNext() {
				return next != null;
			}
			
			public IEntityPart next() {
				final IEntityPart cur = next;
				next = next.next;
				return cur;
			}
			
			/**
			 * Die Funktion ist nicht implementiert.
			 */
			public void remove() {}
		};
	}
	
	/**
	 * Fügt der Entität ein Teil hinzu.
	 * 
	 * @param part das neue Teil
	 */
	protected final void addPart(EntityPart part) {
		tail.next = part;
		tail = part;
	}
	
	/**
	 * Bewegt alle Teile hinter dem Kopf der Entität in die aktuelle Richtung.
	 * 
	 * @see #moveHead()
	 */
	protected final void moveBody() {
		int lastX = head.xPos;
		int lastY = head.yPos;
		int lastR = head.route;
		for (EntityPart part : head) {
			int newX = part.xPos;
			int newY = part.yPos;
			int newR = part.route;
			part.xPos = lastX;
			part.yPos = lastY;
			part.route = lastR;

			lastX = newX;
			lastY = newY;
			lastR = newR;
		}
	}
}
