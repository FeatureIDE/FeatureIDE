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
package de.ovgu.featureide.fm.ui.views.featuremodeleditview;

import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;

/**
 * Returns a label and an image for a given tree element.
 * 
 * @author Thomas Thuem
 */
public class ViewLabelProvider extends LabelProvider implements GUIDefaults {
	
	public ViewLabelProvider() {
	}
	
	public String getText(Object o) {
		return o.toString();
	}

	public Image getImage(Object o) {
		if (o instanceof TreeObject)
			return ((TreeObject) o).getImage();
		if (o instanceof SelectableFeature) {
			SelectableFeature feature = (SelectableFeature) o;
			return feature.getManual() == Selection.SELECTED ? IMAGE_ASELECTED
					: IMAGE_ADESELECTED;
		}
		return null;
	}
	
	@Override
	public void dispose() {
//		IMAGE_ASELECTED.dispose();
//		IMAGE_ADESELECTED.dispose();
		super.dispose();
	}

}
