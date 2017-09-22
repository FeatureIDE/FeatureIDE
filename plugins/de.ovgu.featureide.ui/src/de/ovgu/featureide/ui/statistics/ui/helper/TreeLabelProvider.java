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
package de.ovgu.featureide.ui.statistics.ui.helper;

import org.eclipse.jface.viewers.ColumnLabelProvider;
import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.ui.statistics.core.composite.IToolTip;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * LabelProvider for the {@code FeatureStatisticsView}. <p> Extends the given {@link ColumnLabelProvider} and allows to print tool tips and images on the view.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class TreeLabelProvider extends ColumnLabelProvider {

	@Override
	public String getToolTipText(Object element) {
		if (element instanceof IToolTip) {
			return ((IToolTip) element).getToolTip();
		}
		return null;
	}

	@Override
	public Image getImage(Object element) {
		if (element instanceof Parent) {
			return ((Parent) element).getImage();
		}
		return super.getImage(element);
	}
}
