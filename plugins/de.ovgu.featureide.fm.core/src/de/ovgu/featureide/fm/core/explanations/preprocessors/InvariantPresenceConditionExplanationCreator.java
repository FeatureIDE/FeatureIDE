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
package de.ovgu.featureide.fm.core.explanations.preprocessors;

import org.prop4j.Node;

/**
 * Generates explanations for invariant presence conditions in preprocessor directives.
 *
 * @author Timo G&uuml;nther
 */
public interface InvariantPresenceConditionExplanationCreator extends PreprocessorExplanationCreator<Node, InvariantPresenceConditionExplanation> {

	/**
	 * Returns true if the expression is a tautology or false if it is a contradiction.
	 *
	 * @return true if the expression is a tautology or false if it is a contradiction
	 */
	public boolean isTautology();

	/**
	 * Sets the tautology flag.
	 *
	 * @param tautology true if the expression is a tautology or false if it is a contradiction
	 */
	public void setTautology(boolean tautology);

	/**
	 * Returns the invariant expression to explain.
	 *
	 * @return the invariant expression to explain
	 */
	@Override
	public Node getSubject();

	/**
	 * Returns an explanation why the expression is a contradiction or a tautology.
	 */
	@Override
	public InvariantPresenceConditionExplanation getExplanation() throws IllegalStateException;
}
