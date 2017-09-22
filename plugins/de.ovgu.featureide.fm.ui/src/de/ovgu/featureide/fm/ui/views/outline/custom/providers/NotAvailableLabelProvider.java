/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY_OUTLINE;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;

/**
 * Label provider for displaying a not available message in the outline
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Reimar Schroeter
 * @author Dominic Labsch
 * @author Daniel Psche
 * @author Christopher Sontag
 */
public class NotAvailableLabelProvider extends OutlineLabelProvider {

	@Override
	public Image getImage(Object element) {
		return null;
	}

	@Override
	public String getText(Object element) {
		return element.toString();
	}

	@Override
	public void addListener(ILabelProviderListener listener) {}

	@Override
	public void dispose() {}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return false;
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {}

	@Override
	public void setForeground(TreeItem item, IFile file) {}

	@Override
	public String getLabelProvName() {
		return EMPTY_OUTLINE;
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		return false;
	}

	@Override
	public void init() {

	}

}
