/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.explanations;

/**
 * Generates {@link Explanation explanations}.
 * 
 * @author Timo G&uuml;nther
 */
public interface ExplanationCreator {
	/**
	 * Returns the subject with an attribute to be explained.
	 * Subclasses should override this to provide a subject of a more specific type.
	 * @return the subject with an attribute to be explained
	 */
	public Object getSubject();
	
	/**
	 * Sets the subject with an attribute to be explained.
	 * Subclasses should override this to only allow subjects of a more specific type.
	 * @param subject the subject with an attribute to be explained
	 * @throws IllegalArgumentException if the subject is not of the type expected by the subclass
	 */
	public void setSubject(Object subject) throws IllegalArgumentException;
	
	/**
	 * Returns an explanation for the specified circumstance.
	 * @return an explanation; null if none could be generated
	 * @throws IllegalStateException if the subject or its context is not set
	 */
	public Explanation getExplanation() throws IllegalStateException;
}