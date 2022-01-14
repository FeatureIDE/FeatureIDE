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
package de.ovgu.featureide.fm.attributes.outlineentry;

import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * 
 * Instance of an IAttributeComputation, that computes the count of an attribute in a feature model
 * 
 * @author Chico Sundermann
 */
public class CountAttributeComputation implements IOutlineEntry {

	Configuration config;
	IFeatureAttribute attribute;
	private static final String LABEL = "Number of occurences: ";

	public CountAttributeComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	public int calculateCount() {
		int count = 0;
		if (config.getFeatureModel() instanceof IExtendedFeatureModel) {
			IExtendedFeatureModel fm = (IExtendedFeatureModel) config.getFeatureModel();
			for (IFeature feat : fm.getFeatures()) {
				if (feat instanceof IExtendedFeature) {
					IExtendedFeature efeat = (IExtendedFeature) feat;
					if (efeat.isContainingAttribute(attribute)) {
						count++;
					}
				}
			}
		}
		return count;
	}

	@Override
	public String getLabel() {
		// TODO Auto-generated method stub
		return LABEL + Integer.toString(calculateCount());
	}

	@Override
	public Image getLabelImage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasChildren() {
		return false;
	}

	@Override
	public List<IOutlineEntry> getChildren() {
		return null;
	}

	public boolean supportsType(Object element) {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry#setConfig(de.ovgu.featureide.fm.core.configuration.Configuration)
	 */
	@Override
	public void setConfig(Configuration config) {
		this.config = config;

	}

	@Override
	public void handleDoubleClick() {
		// TODO Auto-generated method stub

	}

}
