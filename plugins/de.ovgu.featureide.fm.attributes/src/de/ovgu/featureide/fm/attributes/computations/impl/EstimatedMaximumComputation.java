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
 * Estimates maximum of a given numerical attribute
 * 
 * @author Chico Sundermann
 */
public class EstimatedMaximumComputation implements IOutlineEntry {

	private static final String LABEL = "Maximal sum of attribute value (est.): ";

	Configuration config;
	IFeatureAttribute attribute;

	public EstimatedMaximumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
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

	@Override
	public boolean supportsType(Object element) {
		return attribute instanceof LongFeatureAttribute || attribute instanceof DoubleFeatureAttribute;
	}

	private List<IFeature> getSelectedLeaves() {
		List<IFeature> selectedFeatures = config.getSelectedFeatures();
		List<IFeature> selectedLeaves = new ArrayList<>();
		for (IFeature feat : selectedFeatures) {
			if (!feat.getStructure().isRoot() && !selectedFeatures.contains(feat.getStructure().getParent().getFeature())) {
				selectedLeaves.add(feat);
			}
		}
		return selectedLeaves;
	}

	private double getSubtreeValue(IFeature root) {
		double value = 0;
		ExtendedFeature ext = (ExtendedFeature) root;
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (att.getName() == attribute.getName()) {
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
			if (root.getStructure().isAnd() || root.getStructure().isOr()) {
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					value = +getSubtreeValue(struc.getFeature());
				}

			} else if (root.getStructure().isAlternative()) {
				double maxValue = 0;
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					double subtreeValue = getSubtreeValue(struc.getFeature());
					if (subtreeValue > maxValue) {
						maxValue = subtreeValue;
					}
				}
				return value + maxValue;
			}
		}
		return 0;
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

}
