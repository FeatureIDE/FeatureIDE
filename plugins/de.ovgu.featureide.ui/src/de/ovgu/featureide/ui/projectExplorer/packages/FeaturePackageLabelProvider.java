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

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IMemento;
import org.eclipse.ui.navigator.ICommonContentExtensionSite;
import org.eclipse.ui.navigator.ICommonLabelProvider;

/**
 * Labels and images of the {@link FeaturePackageRoot source folders} and {@link FeaturePackage packages} in feature folders, using the images of the
 * Package Explorer.
 *
 * @author Philipp Hehnle
 */
public class FeaturePackageLabelProvider extends LabelProvider implements ICommonLabelProvider {

	@Override
	public void init(ICommonContentExtensionSite config) {}

	@Override
	public void restoreState(IMemento memento) {}

	@Override
	public void saveState(IMemento memento) {}

	@Override
	public String getText(Object element) {
		if (element instanceof FeaturePackageRoot) {
			return ((FeaturePackageRoot) element).getLabel();
		} else if (element instanceof FeaturePackage) {
			return ((FeaturePackage) element).getName();
		}
		return null;
	}

	@Override
	public Image getImage(Object element) {
		final ISharedImages images = JavaUI.getSharedImages();
		if (element instanceof FeaturePackageRoot) {
			return images.getImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
		} else if (element instanceof FeaturePackage) {
			return images.getImage(isEmpty((FeaturePackage) element) ? ISharedImages.IMG_OBJS_EMPTY_PACKAGE : ISharedImages.IMG_OBJS_PACKAGE);
		}
		return null;
	}

	/**
	 * Shown in the status bar: the path of the selected node.
	 */
	@Override
	public String getDescription(Object element) {
		if (element instanceof FeaturePackageRoot) {
			return ((FeaturePackageRoot) element).getFolder().getFullPath().makeRelative().toString();
		} else if (element instanceof FeaturePackage) {
			final FeaturePackage featurePackage = (FeaturePackage) element;
			return featurePackage.getName() + " - " + featurePackage.getRoot().getFullPath().makeRelative();
		}
		return null;
	}

	private static boolean isEmpty(FeaturePackage featurePackage) {
		try {
			return !featurePackage.getFolder().exists() || FeaturePackageStructure.getPackageChildren(featurePackage).isEmpty();
		} catch (final CoreException e) {
			return false;
		}
	}
}
