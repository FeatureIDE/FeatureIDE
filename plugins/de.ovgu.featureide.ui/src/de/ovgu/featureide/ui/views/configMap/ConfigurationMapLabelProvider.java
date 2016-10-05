/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.views.configMap;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.color.FeatureColor;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * TODO description
 * 
 * @author gruppe40
 */
public class ConfigurationMapLabelProvider extends ColumnLabelProvider {
	@Override
	public Color getBackground(Object element) {
		if (element instanceof IFeature) {
		FeatureColor fColor = FeatureColorManager.getColor((IFeature) element);
		return fColor.toSwtColor();
		}
		return super.getBackground(element);
	}

	@Override
	public Color getForeground(Object element) {
		return super.getForeground(element);
	}

	@Override
	public Image getImage(Object element) {
		return super.getImage(element);
	}

	@Override
	public String getText(Object element) {
		return element == null ? "NULL" : element.toString();//$NON-NLS-1$
	}
}
