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
package de.ovgu.featureide.ui.views.collaboration.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.IColorProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.TreeItem;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.views.outline.FmLabelProvider;

/**
 * Wrapper for the feature-model label provider
 *
 * @author Reimar Schroeter
 */
public class FMOutlineLabelProviderWrapper extends OutlineLabelProvider implements IColorProvider {

	private final FmLabelProvider prov = new FmLabelProvider();

	@Override
	public Image getImage(Object element) {
		return prov.getImage(element);
	}

	@Override
	public String getText(Object element) {
		if (element instanceof IFeature) {
			return prov.getText(((IFeature)element).getName());
		} else if (element instanceof IConstraint) {
			return prov.getText(((IConstraint)element).getDisplayName());
		} else return prov.getText(element);
	}

	@Override
	public void addListener(ILabelProviderListener listener) {
		prov.addListener(listener);
	}

	@Override
	public void dispose() {
		prov.dispose();
	}

	@Override
	public boolean isLabelProperty(Object element, String property) {
		return prov.isLabelProperty(element, property);
	}

	@Override
	public void removeListener(ILabelProviderListener listener) {
		prov.removeListener(listener);
	}

	@Override
	public void colorizeItems(TreeItem[] treeItems, IFile file) {
		//	prov.colorizeItems(treeItems, file);
	}

	@Override
	public void setForeground(TreeItem item, IFile file) {
	}

	@Override
	public String getLabelProvName() {
		return "Feature-Model Outline";
	}

	@Override
	public int getOutlineType() {
		return OutlineLabelProvider.OUTLINE_FEATURE_MODEL;
	}

	@Override
	public boolean refreshContent(IFile oldFile, IFile currentFile) {
		return false;
	}

	@Override
	public void init() {
	}

	@Override
	public Color getForeground(Object element) {
		return null;
	}

	@Override
	public Color getBackground(Object element) {
		return prov.getBackground(element);
	}

}
