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
package de.ovgu.featureide.fm.attributes.base.impl;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.Feature;

/**
 * Represents extended features by extending {@link Feature}. Provides a list of {@link IFeatureAttribute}.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class ExtendedFeature extends Feature implements IExtendedFeature {

	protected List<IFeatureAttribute> attributes;

	protected ExtendedFeature(ExtendedFeature copyFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(copyFeature, featureModel, newFeatrureStructure);

		// Copy all attributes from the copy feature
		attributes = Collections.synchronizedList(new LinkedList<IFeatureAttribute>());
		for (IFeatureAttribute attribute : copyFeature.getAttributes()) {
			attributes.add(attribute.cloneAtt(this));
		}
	}

	public ExtendedFeature(IFeatureModel featureModel, String name) {
		super(featureModel, name);

		// Create empty attributes list
		attributes = Collections.synchronizedList(new LinkedList<IFeatureAttribute>());
	}

	@Override
	public List<IFeatureAttribute> getAttributes() {
		return attributes;
	}

	@Override
	public void addAttribute(IFeatureAttribute attribute) {
		attributes.add(attribute);
	}

	@Override
	public void removeAttribute(IFeatureAttribute attribute) {
		attributes.remove(attribute);
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new ExtendedFeature(this, newFeatureModel, newStructure);
	}

	@Override
	public boolean isContainingAttribute(IFeatureAttribute attribute) {
		for (IFeatureAttribute att : attributes) {
			if (attribute.getName().equals(att.getName())) {
				return true;
			}
		}
		return false;
	}

	@Override
	public String createTooltip(Object... objects) {
		StringBuilder tooltip = new StringBuilder(super.createTooltip(objects));
		return createExtendedTooltip(attributes, tooltip);
	}

	public static String createExtendedTooltip(List<IFeatureAttribute> attributes, StringBuilder tooltip) {
		tooltip.append("\n\n");

		StringBuilder attributesString = new StringBuilder();
		StringBuilder inhreritedString = new StringBuilder();
		List<IFeatureAttribute> featureAttributes = new ArrayList<>();
		List<IFeatureAttribute> inheritedAttributes = new ArrayList<>();

		if (attributes.size() == 0) {
			tooltip.append("No Attributes.\n");
		} else {// Append attributes as list
			attributesString.append("Attributes:\n");
			inhreritedString.append("Inherited Attributes:\n");
			for (int i = 0; i < attributes.size(); i++) {
				IFeatureAttribute attribute = attributes.get(i);
				if (attributes.get(i).isRecursive() && !attributes.get(i).isHeadOfRecursiveAttribute()) {
					inheritedAttributes.add(attribute);
				} else {
					featureAttributes.add(attribute);
				}
			}

			// Append attributes defined for this feature
			for (int i = 0; i < featureAttributes.size(); i++) {
				IFeatureAttribute iFeatureAttribute = featureAttributes.get(i);
				if (iFeatureAttribute.isRecursive()) {
					attributesString.append("recursive ");
				}
				if (iFeatureAttribute.isConfigurable()) {
					attributesString.append("configureable ");
				}
				attributesString.append(iFeatureAttribute.getType() + " ");
				attributesString.append(iFeatureAttribute.getName() + " = ");
				attributesString.append(iFeatureAttribute.getValue());
				if (iFeatureAttribute.getUnit() != null && !iFeatureAttribute.getUnit().equals("")) {
					attributesString.append(" ");
					attributesString.append(iFeatureAttribute.getUnit());
				}
				if (i < featureAttributes.size() - 1) {
					attributesString.append("\n");
				}
			}

			// Append attributes inherited of this feature
			for (int i = 0; i < inheritedAttributes.size(); i++) {
				IFeatureAttribute iFeatureAttribute = inheritedAttributes.get(i);
				if (iFeatureAttribute.isRecursive()) {
					inhreritedString.append("recursive ");
				}
				if (iFeatureAttribute.isConfigurable()) {
					inhreritedString.append("configureable ");
				}
				inhreritedString.append(iFeatureAttribute.getType() + " ");
				inhreritedString.append(iFeatureAttribute.getName() + " = ");
				inhreritedString.append(iFeatureAttribute.getValue());
				if (iFeatureAttribute.getUnit() != null && !iFeatureAttribute.getUnit().equals("")) {
					inhreritedString.append(" ");
					inhreritedString.append(iFeatureAttribute.getUnit());
				}
				if (i < inheritedAttributes.size() - 1) {
					inhreritedString.append("\n");
				}
			}

			if (!attributesString.toString().equals("Attributes:\n")) {
				tooltip.append(attributesString.toString());
				if (!inhreritedString.toString().equals("Inherited Attributes:\n")) {
					tooltip.append("\n\n" + inhreritedString.toString());
				}
			} else {
				if (!inhreritedString.toString().equals("Inherited Attributes:\\n")) {
					tooltip.append(inhreritedString.toString());
				}
			}
		}
		return tooltip.toString();
	}
}
