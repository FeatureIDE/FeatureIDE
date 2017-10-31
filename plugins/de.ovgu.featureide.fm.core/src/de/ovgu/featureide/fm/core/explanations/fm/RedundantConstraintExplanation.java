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
package de.ovgu.featureide.fm.core.explanations.fm;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;

/**
 * An explanation for redundant constraints in feature models.
 *
 * @author Timo G&uuml;nther
 */
public class RedundantConstraintExplanation extends FeatureModelExplanation<IConstraint> {

	/** True if this explanation is for an implicit constraint. */
	private boolean implicit;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param subject the subject to be explained
	 */
	public RedundantConstraintExplanation(IConstraint subject) {
		super(subject);
	}

	/**
	 * Returns true iff this explanation is for an implicit constraint.
	 *
	 * @return true iff this explanation is for an implicit constraint
	 */
	public boolean isImplicit() {
		return implicit;
	}

	/**
	 * Sets whether this explanation is for an implicit constraint.
	 *
	 * @param implicit whether this explanation is for an implicit constraint
	 */
	public void setImplicit(boolean implicit) {
		this.implicit = implicit;
	}

	@Override
	public Node getImplication() {
		return getSubject().getNode();
	}

	@Override
	public RedundantConstraintExplanationWriter getWriter() {
		return new RedundantConstraintExplanationWriter(this);
	}
}
