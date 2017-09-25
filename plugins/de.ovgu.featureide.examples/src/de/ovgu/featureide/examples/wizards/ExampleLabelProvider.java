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
package de.ovgu.featureide.examples.wizards;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Color;

import de.ovgu.featureide.examples.utils.ProjectRecord;

/**
 * Provides labels for the {@link DynamicContentProvider}.
 *
 * @author Reimar Schroeter
 */
class ExampleLabelProvider extends LabelProvider implements IColorProvider {

	private static final Color YELLOW = new Color(null, 183, 187, 11);
	private static final Color RED = new Color(null, 240, 0, 0);
	private static final Color BLACK = new Color(null, 0, 0, 0);
	private static final Color WHITE = new Color(null, 255, 255, 255);

	@Override
	public String getText(Object element) {
		if (element instanceof ProjectRecord.TreeItem) {
			return ((ProjectRecord.TreeItem) element).toString();
		} else if (element instanceof IPath) {
			return ((IPath) element).lastSegment();
		} else {
			return "";
		}
	}

	@Override
	public Color getForeground(Object element) {
		if (element instanceof ProjectRecord.TreeItem) {
			final ProjectRecord tmpRecord = ((ProjectRecord.TreeItem) element).getRecord();
			if (tmpRecord.hasErrors()) {
				return RED;
			} else if (tmpRecord.hasWarnings()) {
				return YELLOW;
			}
		}
		return BLACK;
	}

	@Override
	public Color getBackground(Object element) {
		return WHITE;
	}

}
