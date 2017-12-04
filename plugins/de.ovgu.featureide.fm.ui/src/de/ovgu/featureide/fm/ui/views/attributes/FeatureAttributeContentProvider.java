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
package de.ovgu.featureide.fm.ui.views.attributes;

import java.util.ArrayList;

import org.eclipse.jface.viewers.ITreeContentProvider;

import de.ovgu.featureide.fm.core.attributes.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * TODO description
 *
 * @author Joshua
 */
public class FeatureAttributeContentProvider implements ITreeContentProvider {

	public static final Object[] EMPTY_ROOT = new Object[] { StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR };

	private IFeatureModel featureModel;
	private Object[] features = EMPTY_ROOT;

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		if (inputElement instanceof IFeatureModel) {
			featureModel = (IFeatureModel) inputElement;
			refreshElements();
			return features;
		} else if (inputElement instanceof Object[]) {
			featureModel = null;
			refreshElements();
			return (Object[]) inputElement;
		} else {
			featureModel = null;
			refreshElements();
			return null;
		}
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getChildren(java.lang.Object)
	 */
	@Override
	public Object[] getChildren(Object parentElement) {
		if (featureModel == null) {
			return null;
		}
		if (parentElement instanceof IFeature) {
			final IFeature feature = (IFeature) parentElement;
			final ArrayList<Object> featureList = new ArrayList<>();
			featureList.addAll(feature.getProperty().getAttributes());
			for (final IFeatureStructure structure : feature.getStructure().getChildren()) {
				featureList.add(structure.getFeature());
			}
			return featureList.toArray();
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object)
	 */
	@Override
	public Object getParent(Object element) {
		if (featureModel == null) {
			return null;
		}
		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			return feature.getStructure().getParent().getFeature();
		} else if (element instanceof IFeatureAttribute) {
			for (final IFeature f : featureModel.getFeatures()) {
				if (f.getProperty().getAttributes().contains(element)) {
					return f;
				}
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.Object)
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof IFeature) {
			final IFeature feature = (IFeature) element;
			return feature.getStructure().hasChildren() || (!feature.getProperty().getAttributes().isEmpty());
		}
		return false;
	}

	private void refreshElements() {
		if (featureModel == null) {
			features = EMPTY_ROOT;
		} else {
			final ArrayList<Object> featureList = new ArrayList<>();
			featureList.add(featureModel.getStructure().getRoot().getFeature());
			features = featureList.toArray();
		}
	}

}
