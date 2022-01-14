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
package de.ovgu.featureide.fm.attributes.view;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 * Implements the {@link ITreeContentProvider} and has the task to provide the content for the {@link FeatureAttributeView}. Structures the feature and their
 * attributes in the same way as the {@link FeatureDiagramEditor}.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeContentProvider implements ITreeContentProvider {

	private IExtendedFeatureModel featureModel;
	private Configuration config;
	private FeatureAttributeView view;

	public FeatureAttributeContentProvider(FeatureAttributeView view) {
		this.view = view;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		switch (view.getMode()) {
		case FEATURE_DIAGRAM:
			if (inputElement instanceof IExtendedFeatureModel) {
				config = null;
				featureModel = (IExtendedFeatureModel) inputElement;
				List<Object> elements = new ArrayList<Object>();
				elements.add(view.getMode().getMessage());
				elements.add(featureModel.getStructure().getRoot().getFeature());
				return elements.toArray();
			}
			break;
		case CONFIGURATION_EDITOR:
			if (inputElement instanceof Configuration) {
				config = (Configuration) inputElement;
				featureModel = (IExtendedFeatureModel) config.getFeatureModel();
				List<Object> elements = new ArrayList<Object>();
				elements.add(view.getMode().getMessage());
				elements.add(featureModel.getStructure().getRoot().getFeature());
				return elements.toArray();
			}
			break;
		default:
			return new Object[] { view.getMode().getMessage() };
		}
		return null;
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
		if (parentElement instanceof IExtendedFeature) {
			final IExtendedFeature feature = (IExtendedFeature) parentElement;
			final ArrayList<Object> featureList = new ArrayList<>();
			// Add all attributes
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
		if (element instanceof IExtendedFeature) {
			final IExtendedFeature feature = (IExtendedFeature) element;
			return feature.getStructure().getParent() != null ? feature.getStructure().getParent().getFeature() : null;
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
		if (element instanceof IExtendedFeature) {
			final IExtendedFeature feature = (IExtendedFeature) element;
			return feature.getStructure().hasChildren() || (!feature.getAttributes().isEmpty());
		}
		return false;
	}

}
