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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;

/**
 * Sorts the content of feature folders like the Package Explorer: source folders, the default package, the other packages, folders and files, each by
 * name.
 *
 * @author Philipp Hehnle
 */
public class FeaturePackageSorter extends ViewerComparator {

	@Override
	public int category(Object element) {
		if (element instanceof FeaturePackageRoot) {
			return 0;
		} else if (element instanceof FeaturePackage) {
			return ((FeaturePackage) element).isDefaultPackage() ? 1 : 2;
		} else if (element instanceof IFolder) {
			return 3;
		} else if (element instanceof IFile) {
			return 4;
		}
		return 5;
	}

	@Override
	public int compare(Viewer viewer, Object e1, Object e2) {
		final int category1 = category(e1);
		final int category2 = category(e2);
		if (category1 != category2) {
			return category1 - category2;
		}
		return getComparator().compare(getName(e1), getName(e2));
	}

	private static String getName(Object element) {
		if (element instanceof FeaturePackageRoot) {
			return ((FeaturePackageRoot) element).getLabel();
		} else if (element instanceof FeaturePackage) {
			return ((FeaturePackage) element).getName();
		} else if (element instanceof IResource) {
			return ((IResource) element).getName();
		}
		return String.valueOf(element);
	}
}
