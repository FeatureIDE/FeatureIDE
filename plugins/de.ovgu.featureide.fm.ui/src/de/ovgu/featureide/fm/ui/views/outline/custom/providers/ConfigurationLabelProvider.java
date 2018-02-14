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
package de.ovgu.featureide.fm.ui.views.outline.custom.providers;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.ui.views.outline.computations.ComputationHeader;
import de.ovgu.featureide.fm.ui.views.outline.computations.IConfigurationComputation;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;

/**
 * TODO description
 *
 * @author Chico Sundermann
 */
public class ConfigurationLabelProvider extends OutlineLabelProvider {

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 */
	@Override
	public Image getImage(Object element) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
	 */
	@Override
	public String getText(Object element) {
		if (element == null) {
			return "Invalid element!";
		}
		if (element instanceof ComputationHeader) {
			return ((ComputationHeader) element).getName();
		}
		if (element instanceof IConfigurationComputation) {
			return ((IConfigurationComputation) element).getResultString();
		}
		return element.toString();
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#addListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void addListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#dispose()
	 */
	@Override
	public void dispose() {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#isLabelProperty(java.lang.Object, java.lang.String)
	 */
	@Override
	public boolean isLabelProperty(Object element, String property) {
		// TODO Auto-generated method stub
		return false;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#removeListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	@Override
	public void removeListener(ILabelProviderListener listener) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#init()
	 */
	@Override
	public void init() {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#getOutlineType()
	 */
	@Override
	public int getOutlineType() {
		// TODO Auto-generated method stub
		return 0;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#colorizeItems(org.eclipse.swt.widgets.TreeItem[],
	 * org.eclipse.core.resources.IFile)
	 */
	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#setForeground(org.eclipse.swt.widgets.TreeItem, org.eclipse.core.resources.IFile)
	 */
	@Override
	public void setForeground(TreeItem item, IFile file) {
		// TODO Auto-generated method stub

	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#getLabelProvName()
	 */
	@Override
	public String getLabelProvName() {
		// TODO Auto-generated method stub
		return "Configuration Outline";
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider#refreshContent(org.eclipse.core.resources.IFile,
	 * org.eclipse.core.resources.IFile)
	 */
	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		// TODO Auto-generated method stub
		return false;
	}

}
