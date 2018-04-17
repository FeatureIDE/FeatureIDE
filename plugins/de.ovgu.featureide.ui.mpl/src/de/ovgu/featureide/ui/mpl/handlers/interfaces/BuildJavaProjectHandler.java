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
package de.ovgu.featureide.ui.mpl.handlers.interfaces;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.fm.ui.handlers.base.AFolderHandler;
import de.ovgu.featureide.ui.mpl.MPLUIPlugin;

/**
 * Action to create a java project from a selected interface.
 *
 * @author Sebastian Krieter
 */
public class BuildJavaProjectHandler extends AFolderHandler {

	@Override
	protected void singleAction(IFolder folder) {
		IResource[] members = null;
		try {
			members = folder.members();
		} catch (final CoreException e) {
			MPLUIPlugin.getDefault().logError(e);
		}

		// TODO Build java projects
//		if (members != null) {
//			for (IResource resource : members) {
//				if (resource.getName().endsWith(IOConstants.EXTENSION_SOLUTION) && resource instanceof IFile) {
//					MPLPlugin.getDefault().buildJavaProject((IFile) resource, folder.getName());
//					break;
//				}
//			}
//		}
	}

}
