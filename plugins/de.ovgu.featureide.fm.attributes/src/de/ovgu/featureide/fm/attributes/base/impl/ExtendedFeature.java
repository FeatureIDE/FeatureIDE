package de.ovgu.featureide.fm.attributes.base.impl;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.impl.Feature;

public class ExtendedFeature extends Feature {

	protected List<IFeatureAttribute> attributes;

	protected ExtendedFeature(ExtendedFeature copyFeature, IFeatureModel featureModel, IFeatureStructure newFeatrureStructure) {
		super(copyFeature, featureModel, newFeatrureStructure);

		// Copy all attributes from the copy feature
		attributes = new ArrayList<>();
		for (IFeatureAttribute attribute : copyFeature.getAttributes()) {
			attributes.add(attribute);
		}
	}

	public ExtendedFeature(IFeatureModel featureModel, String name) {
		super(featureModel, name);

		// Create empty attributes list
		attributes = new ArrayList<>();
	}

	public List<IFeatureAttribute> getAttributes() {
		return Collections.unmodifiableList(attributes);
	}

	public void addAttribute(IFeatureAttribute attribute) {
		attributes.add(attribute);
	}

	public void removeAttribute(IFeatureAttribute attribute) {
		attributes.remove(attribute);
	}

	public void setAttributes(List<IFeatureAttribute> attributes) {
		this.attributes = attributes;
	}

	@Override
	public IFeature clone(IFeatureModel newFeatureModel, IFeatureStructure newStructure) {
		return new ExtendedFeature(this, newFeatureModel, newStructure);
	}

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
		tooltip.append("\n\n");
		StringBuilder attributesString = new StringBuilder();
		StringBuilder inhreritedString = new StringBuilder();
		if (attributes.size() == 0) {
			tooltip.append("No Attributes.\n");
		} else {// Append attributes as list
			attributesString.append("Attributes:\n");
			inhreritedString.append("Inherited Attributes:\n");
			for (int i = 0; i < attributes.size(); i++) {
				IFeatureAttribute attribute = attributes.get(i);

				if (attributes.get(i).isRecursive() && !attributes.get(i).isHeadOfRecursiveAttribute()) {
					if (attributes.get(i).isRecursive()) {
						inhreritedString.append("recursive ");
					}
					if (attributes.get(i).isConfigurable()) {
						inhreritedString.append("configureable ");
					}
					inhreritedString.append(attribute.getType() + " ");
					inhreritedString.append(attribute.getName() + " = ");
					inhreritedString.append(attribute.getValue());
					if (attribute.getUnit() != null && !attribute.getUnit().equals("")) {
						inhreritedString.append(" ");
						inhreritedString.append(attribute.getUnit());
					}
					if (i < attributes.size() - 1) {
						inhreritedString.append("\n");
					}
				} else {
					if (attributes.get(i).isRecursive()) {
						attributesString.append("recursive ");
					}
					if (attributes.get(i).isConfigurable()) {
						attributesString.append("configureable ");
					}
					attributesString.append(attribute.getType() + " ");
					attributesString.append(attribute.getName() + " = ");
					attributesString.append(attribute.getValue());
					if (attribute.getUnit() != null && !attribute.getUnit().equals("")) {
						attributesString.append(" ");
						attributesString.append(attribute.getUnit());
					}
					if (i < attributes.size() - 1) {
						attributesString.append("\n");
					}
				}
			}

			tooltip.append(attributesString.toString());
			if (!inhreritedString.toString().equals("Inherited Attributes:\\n")) {
				tooltip.append("\n" + inhreritedString.toString());
			}
		}
		return tooltip.toString();

	}
}
