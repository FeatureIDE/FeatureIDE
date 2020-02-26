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

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 * Realizes filtering for the {@link FeatureAttributeView}. Only selected features of the {@link FeatureDiagramEditor} are shown when the filter is activated.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class FeatureAttributeViewSelectionFilter extends ViewerFilter {

	private FeatureAttributeView faView;

	FeatureAttributeViewSelectionFilter(FeatureAttributeView faView) {
		this.faView = faView;
	}

	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		if (faView.getSelectedFeatures() == null || faView.getSelectedFeaturesOfInterest() == null) {
			if (faView.getFeatureModel() != null) {
				return element == FeatureAttributeContentProvider.SELECT_FEATURES_IN_FEATURE_DIAGRAM;
			} else {
				return true;
			}
		} else {
			if (faView.getSelectedFeatures().size() == 0 || faView.getSelectedFeaturesOfInterest().size() == 0) {
				if (faView.getFeatureModel() != null) {
					return element == FeatureAttributeContentProvider.SELECT_FEATURES_IN_FEATURE_DIAGRAM;
				} else {
					return true;
				}
			} else {
				if (viewer instanceof TreeViewer) {
					if (element instanceof IFeature && faView.getSelectedFeatures().contains(element)) {
						return true;
					} else if (element instanceof IFeatureAttribute && faView.getSelectedFeaturesOfInterest().contains(parentElement)) {
						return true;
					} else {
						return false;
					}
				}
			}
		}
		return false;
	}

}
