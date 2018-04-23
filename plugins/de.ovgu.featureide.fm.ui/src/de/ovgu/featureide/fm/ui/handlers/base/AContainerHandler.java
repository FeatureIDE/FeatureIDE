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

import org.eclipse.core.resources.IContainer;

/**
 * Abstract class for handlers that work on containers (IProject and IFolder).
 *
 * @author Sebastian Krieter
 */
public abstract class AContainerHandler extends ASelectionHandler {

	/**
	 * This method is called for every container in the current selection.
	 *
	 * @param container the current container handle.
	 */
	protected abstract void singleAction(IContainer container);

	@Override
	protected void singleAction(Object element) {
		final IContainer container = SelectionWrapper.checkClass(element, IContainer.class);
		if (container != null) {
			singleAction(container);
		}
	}
}
