/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.editors.featuremodel.filters;

import java.util.function.Predicate;

import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;

/**
 * Checks whether a graphical feature is optional.
 *
 * @author Christopher Sontag
 * @author Johannes Herschel
 */
public class OptionalGraphicalFeatureFilter implements Predicate<IGraphicalFeature> {

	@Override
	public boolean test(IGraphicalFeature object) {
		final IFeatureStructure structure = object.getObject().getStructure();
		final IFeatureStructure parent = structure.getParent();
		return (parent != null) && parent.isAnd() && !structure.isMandatory();
	}

}
