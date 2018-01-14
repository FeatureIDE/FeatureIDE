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
package de.ovgu.featureide.fm.attributes.view;

import java.util.ArrayList;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * TODO description
 *
 * @author Joshua Sprey
 */
public class FeatureAttributeContentProvider implements ITreeContentProvider {

	public static final Object[] EMPTY_ROOT = new Object[] { StringTable.PLEASE_OPEN_A_FEATURE_DIAGRAM_EDITOR };
	public static final Object[] FALSE_MODEL_FORMAT = new Object[] { StringTable.MODEL_NOT_SUPPORTED_PLEASE_CONVERT_TO_EXTENDED_MODEL };

	private ExtendedFeatureModel featureModel;
	private Object[] features = EMPTY_ROOT;
	private TreeViewer viewer;

	public FeatureAttributeContentProvider(TreeViewer viewer) {
		this.viewer = viewer;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		if (inputElement instanceof ExtendedFeatureModel) {
			featureModel = (ExtendedFeatureModel) inputElement;
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
		if (parentElement instanceof ExtendedFeature) {
			final ExtendedFeature feature = (ExtendedFeature) parentElement;
			final ArrayList<Object> featureList = new ArrayList<>();
			featureList.addAll(feature.getAttributes());
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
		if (element instanceof ExtendedFeature) {
			final ExtendedFeature feature = (ExtendedFeature) element;
			return feature.getStructure().getParent().getFeature();
		} else if (element instanceof IFeatureAttribute) {
			return ((IFeatureAttribute) element).getFeature();
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.Object)
	 */
	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof ExtendedFeature) {
			final ExtendedFeature feature = (ExtendedFeature) element;
			return feature.getStructure().hasChildren() || (!feature.getAttributes().isEmpty());
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
