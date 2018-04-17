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
package de.ovgu.featureide.ui.properties;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.UIPlugin;

/**
 *
 * Checks whether the selected element can be run as integration test.
 *
 * @author Jens Meinicke
 */
public class IntegrationTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		if (receiver instanceof IFolder) {
			final IFolder selectedFolder = (IFolder) receiver;
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(selectedFolder);
			if ((featureProject != null) && featureProject.getComposer().hasFeatureFolder()) {
				final IFolder sourceFolder = featureProject.getSourceFolder();
				try {
					for (final IResource featureFolder : sourceFolder.members()) {
						if (selectedFolder.equals(featureFolder)) {
							return true;
						}
					}
				} catch (final CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}
		}
		return false;
	}

}
