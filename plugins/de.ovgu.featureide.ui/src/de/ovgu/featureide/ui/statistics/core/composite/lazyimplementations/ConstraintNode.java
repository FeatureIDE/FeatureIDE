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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINT;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * Convenience-class to evaluate constraints which is just extracting their names.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class ConstraintNode extends LazyParent {

	protected final IConstraint constr;

	public ConstraintNode(IConstraint constr) {
		super(CONSTRAINT, constr.toString());
		this.constr = constr;
		lazy = false;
	}

	@Override
	protected void initChildren() {}
}
