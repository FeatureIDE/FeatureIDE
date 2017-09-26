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
package de.ovgu.featureide.fm.ui.views.outline.custom;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.TreeItem;

/**
 * Label provider for each FeatureIDE outline
 *
 * @author Reimar Schr�ter
 */
public abstract class OutlineLabelProvider implements ILabelProvider {

	public static final int OUTLINE_NOT_AVAILABLE = -1;
	public static final int OUTLINE_FEATURE_MODEL = 0;
	public static final int OUTLINE_CODE = 1;

	protected TreeViewer viewer;

	public void initTreeViewer(TreeViewer viewer) {
		this.viewer = viewer;
		init();
	}

	public abstract void init();

	public abstract int getOutlineType();

	/**
	 * colors the TreeItems gray in case the method/field is not in the current file<br> makes the TreeItems bold in case the Feature inside the TreeItem is in
	 * the current file
	 *
	 * @param treeItems the items that should be colored
	 * @param file
	 */
	public abstract void colorizeItems(TreeItem[] treeItems, IFile file);

	public abstract void setForeground(TreeItem item, IFile file);

	public abstract String getLabelProvName();

	public abstract boolean refreshContent(IFile oldFile, IFile currentFile); // TreeItem[]
																				 // items,
}
