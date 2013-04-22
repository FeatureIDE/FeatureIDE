/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
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
