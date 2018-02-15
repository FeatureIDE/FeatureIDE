package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.FMAttributesPlugin;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * 
 * TODO description
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
		return attribute.getName();
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
		EstimatedMinimumComputation min = new EstimatedMinimumComputation(config, attribute);
		EstimatedMaximumComputation max = new EstimatedMaximumComputation(config, attribute);
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
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public void setConfig(Configuration config) {
		// TODO Auto-generated method stub

	}

}
