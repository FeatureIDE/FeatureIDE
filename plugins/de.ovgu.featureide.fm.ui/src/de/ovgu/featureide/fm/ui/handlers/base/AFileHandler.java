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
package de.ovgu.featureide.fm.ui.handlers.base;

import org.eclipse.core.resources.IFile;

/**
 * Abstract class for handlers that work on files.
 *
 * @author Sebastian Krieter
 */
public abstract class AFileHandler extends ASelectionHandler {

	/**
	 * This method is called for every file in the current selection.
	 *
	 * @param file the current file handle.
	 */
	protected abstract void singleAction(IFile file);

	@Override
	protected void singleAction(Object element) {
		final IFile file = SelectionWrapper.checkClass(element, IFile.class);
		if (file != null) {
			singleAction(file);
		}
	}
}
