package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.IExtendedFeatureModel;
import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.outlineentry.AttributeEntry;
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
		return "Attribute calculations";
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
		return config.getFeatureModel() instanceof IExtendedFeatureModel;
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
