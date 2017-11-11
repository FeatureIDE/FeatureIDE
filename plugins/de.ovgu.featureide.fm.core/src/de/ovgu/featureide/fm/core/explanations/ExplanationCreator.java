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
 * @param <S> subject
 * @param <E> explanation
 * @author Timo G&uuml;nther
 */
public interface ExplanationCreator<S, E extends Explanation<S>> {

	/**
	 * Returns the subject with an attribute to be explained.
	 *
	 * @return the subject with an attribute to be explained
	 */
	public S getSubject();

	/**
	 * Sets the subject with an attribute to be explained.
	 *
	 * @param subject the subject with an attribute to be explained
	 */
	public void setSubject(S subject);

	/**
	 * Returns an explanation for the specified circumstance.
	 *
	 * @return an explanation; null if none could be generated
	 * @throws IllegalStateException if the subject or its context is not set
	 */
	public E getExplanation() throws IllegalStateException;
}
