/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.projectExplorer.packages;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;

/**
 * Properties of resources in the namespace <code>de.ovgu.featureide.ui.projectExplorer</code>, used in plugin.xml:
 * <ul>
 * <li><code>isFeatureFolder</code>: whether a folder is a feature folder whose content is shown as packages.</li>
 * <li><code>isInFeatureFolder</code>: whether a resource is inside such a feature folder (and not the feature folder itself).</li>
 * </ul>
 *
 * @author Philipp Hehnle
 */
public class FeatureFolderPropertyTester extends PropertyTester {

	@Override
	public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
		if ("isFeatureFolder".equals(property)) {
			return FeatureFolders.isFeatureFolder(receiver);
		} else if ("isInFeatureFolder".equals(property) && (receiver instanceof IResource)) {
			final IFolder featureFolder = FeatureFolders.getFeatureFolder((IResource) receiver);
			return (featureFolder != null) && !featureFolder.equals(receiver);
		}
		return false;
	}
}
