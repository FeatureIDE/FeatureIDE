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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.config.ExtendedConfiguration;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * 
 * Creates a list with the computations used in the Attribute calculations outline
 * 
 * @author Chico Sundermann
 */
public class AttributeComputationBundle implements IOutlineEntry {

	Configuration config;

	@Override
	public String getLabel() {
		// TODO Auto-generated method stub
		return "Attribute statistics";
	}

	@Override
	public Image getLabelImage() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public List<IOutlineEntry> getChildren() {
		List<IOutlineEntry> children = new ArrayList<>();
		for (IFeatureAttribute att : getUniqueAttributes()) {
			children.add(new AttributeEntry(config, att));
		}
		return children;
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
	public boolean supportsType(Object element) {
		boolean isExtendedFeatureModel = config.getFeatureModel() instanceof IExtendedFeatureModel;
		boolean isExtendedConfiguration = config instanceof ExtendedConfiguration;
		return isExtendedFeatureModel && isExtendedConfiguration;
	}

	private List<IFeatureAttribute> getUniqueAttributes() {
		List<IFeatureAttribute> attributeList = new ArrayList<IFeatureAttribute>();
		for (IFeature feat : config.getFeatureModel().getFeatures()) {
			if (feat instanceof IExtendedFeature) {
				for (IFeatureAttribute att : ((IExtendedFeature) feat).getAttributes()) {
					if (!containsAttribute(attributeList, att.getName())) {
						attributeList.add(att);
					}
				}
			}
		}
		return attributeList;
	}

	private boolean containsAttribute(List<IFeatureAttribute> list, String attributeName) {
		for (IFeatureAttribute att : list) {
			if (att.getName().equals(attributeName)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void handleDoubleClick() {
		// TODO Auto-generated method stub

	}

}
