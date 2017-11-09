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
package de.ovgu.featureide.fm.ui;

import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.gef.AutoexposeHelper;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;

import de.ovgu.featureide.fm.ui.utils.FullViewportAutoexposeHelper;

/**
 * Provides a better DND auto scroll behavior
 */
public class ChillScrollFreeformRootEditPart extends ScalableFreeformRootEditPart {

	@Override
	public Object getAdapter(Class adapter) {
		if (adapter == AutoexposeHelper.class) {
			Insets insets = new Insets(50);
			float speed = 2;
			return new FullViewportAutoexposeHelper(this, insets, speed);
		}
		return super.getAdapter(adapter);
	}

}
