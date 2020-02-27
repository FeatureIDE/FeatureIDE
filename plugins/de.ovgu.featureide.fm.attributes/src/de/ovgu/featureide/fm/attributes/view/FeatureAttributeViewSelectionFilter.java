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

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView.FeatureAttributeOperationMode;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
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
		if (faView.getMode() == FeatureAttributeOperationMode.FEATURE_DIAGRAM) {
			return filterFeatureModel(viewer, parentElement, element);
		} else if (faView.getMode() == FeatureAttributeOperationMode.CONFIGURATION_EDITOR) {
			return filterConfiguration(viewer, parentElement, element);
		}
		return true;
	}

	private boolean filterFeatureModel(Viewer viewer, Object parentElement, Object element) {
		if (element.equals(faView.getMode().getMessage())) {
			return faView.getSelectedFeatures().isEmpty();
		} else if (element instanceof IFeature && faView.getSelectedFeatures().contains(element)) {
			return true;
		} else if (element instanceof IFeatureAttribute && faView.getSelectedFeaturesOfInterest().contains(parentElement)) {
			return true;
		} else {
			return false;
		}
	}

	private boolean filterConfiguration(Viewer viewer, Object parentElement, Object element) {
		ConfigurationManager manager = (ConfigurationManager) faView.getManager();
		if (element.equals(faView.getMode().getMessage())) {
			return manager.getVarObject().getFeatureModel().getFeatures().stream().filter(this::isConfigurableFeature).count() <= 0;
		} else if (element instanceof IFeature) {
			ExtendedFeature feat = (ExtendedFeature) element;
			if (manager.getVarObject().getSelectableFeature(feat).getSelection() == Selection.SELECTED) {
				return feat.getAttributes().stream().filter(this::isConfigurableAttribute).count() > 0;
			} else {
				return false;
			}
		} else if (element instanceof IFeatureAttribute) {
			return ((IFeatureAttribute) element).isConfigurable();
		}
		return false;
	}

	private boolean isConfigurableAttribute(IFeatureAttribute att) {
		return att.isConfigurable();
	}

	private boolean isConfigurableFeature(IFeature feat) {
		ExtendedFeature ext = (ExtendedFeature) feat;
		return ext.getAttributes().stream().filter(this::isConfigurableAttribute).count() > 0;
	}

}
