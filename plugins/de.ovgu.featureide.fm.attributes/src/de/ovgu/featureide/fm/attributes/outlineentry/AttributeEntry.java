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

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * 
 * Outline entry representing an feature attribute Attribute, computations are supposed to be attached to this
 * 
 * @author Chico Sundermann
 */
public class AttributeEntry implements IOutlineEntry {

	private Configuration config;

	private IFeatureAttribute attribute;

	private final static String imgAttribute = "attribute_obj.ico";

	public AttributeEntry(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	@Override
	public String getLabel() {
		// TODO Auto-generated method stub
		return attribute.getName() + " (" + attribute.getType() + ")";
	}

	@Override
	public Image getLabelImage() {
		// TODO Attribute icon
		return FMAttributesPlugin.getImage(imgAttribute);
	}

	@Override
	public boolean hasChildren() {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public List<IOutlineEntry> getChildren() {
		List<IOutlineEntry> children = new ArrayList<>();
		children.add(new CountAttributeComputation(config, attribute));
		AttributeMinimumEntry min = new AttributeMinimumEntry(config, attribute);
		AttributeMaximumEntry max = new AttributeMaximumEntry(config, attribute);
		if (min.supportsType(null)) {
			children.add(min);
		}
		if (max.supportsType(null)) {
			children.add(max);
		}
		return children;
	}

	@Override
	public boolean supportsType(Object element) {
		return true;
	}

	@Override
	public void setConfig(Configuration config) {
		this.config = config;

	}

	@Override
	public void handleDoubleClick() {
		// TODO Auto-generated method stub

	}

}
