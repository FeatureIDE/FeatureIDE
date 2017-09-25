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
package de.ovgu.featureide.ui.handlers.base;

import org.eclipse.core.resources.IResource;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.ui.handlers.base.ASelectionHandler;
import de.ovgu.featureide.fm.ui.handlers.base.SelectionWrapper;

/**
 * Abstract class for handlers that work on projects.
 *
 * @author Sebastian Krieter
 */
public abstract class AFeatureProjectHandler extends ASelectionHandler {

	/**
	 * This method is called for every project in the current selection.
	 *
	 * @param project the current project handle.
	 */
	protected abstract void singleAction(IFeatureProject project);

	@Override
	protected void singleAction(Object element) {
		final IResource res = SelectionWrapper.checkClass(element, IResource.class);
		final IFeatureProject featureProject = CorePlugin.getFeatureProject(res);
		if (featureProject != null) {
			singleAction(featureProject);
		}
	}
}
