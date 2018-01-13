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

	protected List<IFeatureAttribute> recursiveAttributes;

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

	public List<IFeatureAttribute> getRecursiveAttributes() {
		return Collections.unmodifiableList(recursiveAttributes);
	}

	public void addRecursiveAttribute(IFeatureAttribute attribute) {
		recursiveAttributes.add(attribute);
	}

	public void removeRecursiveAttribute(IFeatureAttribute attribute) {
		recursiveAttributes.remove(attribute);
	}

	public void setRecursiveAttributes(List<IFeatureAttribute> recursiveAttributes) {
		this.recursiveAttributes = recursiveAttributes;
	}

	public boolean isContainingAttribute(IFeatureAttribute attribute) {
		for (IFeatureAttribute att : attributes) {
			if (attribute.getName().equals(att.getName())) {
				return true;
			}
		}
		return false;
	}
}
