package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.swt.graphics.Image;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.ui.views.outline.IOutlineEntry;

/**
 * Estimates the minimum of a numerical attribute given a partial configuration Only supposed to be used on numerical attributes
 * 
 * @author Chico Sundermann
 */
public class EstimatedMinimumComputation implements IOutlineEntry {

	private static final String LABEL = "Minimal sum of attribute value (est.): ";
	Configuration config;
	IFeatureAttribute attribute;

	public EstimatedMinimumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	private Object getSelectionSum() {
		double sum = 0.0;
		List<IFeature> selectedFeatures = config.getSelectedFeatures();
		List<IFeature> selectedLeaves = getSelectedLeaves();
		selectedFeatures.removeAll(selectedLeaves);
		for (IFeature feat : selectedLeaves) {
			sum += getSubtreeValue(feat);
		}
		for (IFeature feat : selectedFeatures) {
			if (feat instanceof ExtendedFeature) {
				ExtendedFeature ext = (ExtendedFeature) feat;
				if (ext.isContainingAttribute(attribute)) {
					for (IFeatureAttribute att : ext.getAttributes()) {
						if (att.getName().equals(attribute.getName())) {
							if (att.getValue() instanceof Long) {
								sum += (long) att.getValue();
							} else if (att.getValue() instanceof Double) {
								sum += (double) att.getValue();
							}
						}
					}
				}
			}
		}
		return sum;
	}

	@Override
	public boolean supportsType(Object element) {
		return attribute instanceof LongFeatureAttribute || attribute instanceof DoubleFeatureAttribute;
	}

	@Override
	public String getLabel() {
		if (attribute instanceof LongFeatureAttribute) {
			return LABEL + String.valueOf(((Double) getSelectionSum()).longValue());
		}
		return LABEL + getSelectionSum().toString();
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

	@Override
	public void setConfig(Configuration config) {
		this.config = config;
	}

	private List<IFeature> getSelectedLeaves() {
		List<IFeature> selectedFeatures = config.getSelectedFeatures();
		List<IFeature> selectedLeaves = new ArrayList<>();
		for (IFeature feat : selectedFeatures) {
			if (!feat.getStructure().hasChildren()) {
				selectedLeaves.add(feat);
			} else {
				boolean isLeave = true;
				for (IFeatureStructure childrenStruct : feat.getStructure().getChildren()) {
					if (selectedFeatures.contains(childrenStruct.getFeature())) {
						isLeave = false;
					}
				}
				if (isLeave) {
					selectedLeaves.add(feat);
				}
			}
		}
		return selectedLeaves;
	}

	private double getSubtreeValue(IFeature root) {
		double value = 0;
		ExtendedFeature ext = (ExtendedFeature) root;
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (att.getName().equals(attribute.getName())) {
				if (att instanceof LongFeatureAttribute) {
					value += (long) att.getValue();
				} else if (att instanceof DoubleFeatureAttribute) {
					value += (double) att.getValue();
				}
			}
		}
		if (!root.getStructure().hasChildren()) {
			return value;
		} else {
			if (root.getStructure().isAnd()) {
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					if (struc.isMandatory()) {
						value = +getSubtreeValue(struc.getFeature());
					}
				}

			} else if (root.getStructure().isAlternative() || root.getStructure().isOr()) {
				double minValue = 0;
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					double subtreeValue = getSubtreeValue(struc.getFeature());
					if (subtreeValue < minValue || minValue == 0) {
						minValue = subtreeValue;
					}
				}
				return value + minValue;
			}
		}
		return 0;
	}

}
