/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2020  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.base.event;

import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;

/**
 * {@link ReferenceEventListener} provides an extension to {@link IEventListener} that allows direct access to a {@link MultiFeatureModel} it manages. This
 * might be useful for propagating updates that occur in a referenced model, for example.
 *
 * @author Benedikt Jutz
 */
public interface ReferenceEventListener extends IEventListener {

	/**
	 * Returns the managed {@link MultiFeatureModel} of this object.
	 *
	 * @return {@link MultiFeatureModel}
	 */
	MultiFeatureModel getFeatureModel();
}
