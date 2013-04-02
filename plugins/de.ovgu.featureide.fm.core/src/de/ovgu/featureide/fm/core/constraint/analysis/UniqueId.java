package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.concurrent.atomic.AtomicInteger;

/**
 * Provides a simple and thread-safe way to generate successive natural numbers.
 * 
 * @author Sebastian Henneberg
 */
public class UniqueId {

	/**
	 * The id generator.
	 */
	private AtomicInteger idGenerator;
	
	/**
	 * Creates an unique id generator instance and initializes internal state. 
	 */
	public UniqueId() {
		idGenerator = new AtomicInteger();
		idGenerator.set(0);
	}
	
	/**
	 * Yields the next free natural number.
	 * 
	 * @return The next free natural number.
	 */
	public int getNext() {
		return idGenerator.incrementAndGet();
	}
}
