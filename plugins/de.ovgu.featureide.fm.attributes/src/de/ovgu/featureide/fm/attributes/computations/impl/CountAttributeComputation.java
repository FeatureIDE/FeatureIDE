package de.ovgu.featureide.fm.attributes.computations.impl;

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

	private int calculateCount() {
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
