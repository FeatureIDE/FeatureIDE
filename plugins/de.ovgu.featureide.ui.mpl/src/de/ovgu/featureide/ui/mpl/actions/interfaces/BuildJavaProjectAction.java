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
package de.ovgu.featureide.ui.mpl.actions.interfaces;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.IOConstants;
import de.ovgu.featureide.ui.mpl.MPLUIPlugin;
import de.ovgu.featureide.ui.mpl.actions.AAction;

/**
 * Action to create a java project from a selected interface.
 * 
 * @author Sebastian Krieter
 */
public class BuildJavaProjectAction extends AAction  {
	@Override
	protected void singleAction(Object element) {
		IFolder folder = null;
		if (element instanceof IFolder) {
			folder = (IFolder) element;
		} else if (element instanceof IAdaptable) {
			folder = (IFolder) ((IAdaptable) element).getAdapter(IFolder.class);
		}
		if (folder != null) {
			IResource[] members = null;
			try {
				members = folder.members();
			} catch (CoreException e) {
				MPLUIPlugin.getDefault().logError(e);
			}
			
			if (members != null) {
				for (IResource resource : members) {
					if (resource.getName().endsWith(IOConstants.EXTENSION_SOLUTION) && resource instanceof IFile) {
						MPLPlugin.getDefault().buildJavaProject((IFile) resource, folder.getName());
						break;
					}
				}
			}
		}
	}
}
