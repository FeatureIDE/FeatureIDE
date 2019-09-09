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
package de.ovgu.featureide.fm.attributes.computations.impl;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.DoubleFeatureAttribute;
import de.ovgu.featureide.fm.attributes.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.attributes.base.impl.LongFeatureAttribute;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Estimates maximum of a given numerical attribute
 * 
 * @author Chico Sundermann
 */
public class EstimatedMaximumComputation {

	private static final String LABEL = "Maximal sum of attribute value (est.): ";

	Configuration config;
	IFeatureAttribute attribute;
	List<IFeature> selectedFeatures;
	List<IFeature> unselectedFeatures;

	public EstimatedMaximumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	private double getSubtreeMaximum(IFeature root) {
		double value = 0;
		ExtendedFeature ext = (ExtendedFeature) root;
		for (IFeatureAttribute att : ext.getAttributes()) {
			if (att.getName().equals(attribute.getName())) {
				if (att instanceof LongFeatureAttribute) {
					if (!(att.getValue() == null)) {
						value += (long) att.getValue();
					}
				} else if (att instanceof DoubleFeatureAttribute) {
					if (!(att.getValue() == null)) {
						value += (double) att.getValue();
					}
				}
			}
		}
		if (!root.getStructure().hasChildren()) {
			return value;
		} else {
			if (root.getStructure().isOr()) {
				List<Double> negativeValues = new ArrayList<>();
				int unselectedCount = 0;
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					if (isUnselected(struc.getFeature())) {
						unselectedCount++;
					} else {
						double tempValue = getSubtreeMaximum(struc.getFeature());
						if (tempValue >= 0 || isSelected(struc.getFeature())) {
							value += tempValue;
						} else {
							negativeValues.add(getSubtreeMaximum(struc.getFeature()));
						}
					}
				}
				if (negativeValues.size() + unselectedCount == root.getStructure().getChildrenCount()) {
					double max = negativeValues.get(0);
					for (double temp : negativeValues) {
						if (temp >= max) {
							max = temp;
						}
					}
					value += max;
				}
			} else if (root.getStructure().isAnd()) {
				for (IFeatureStructure struct : root.getStructure().getChildren()) {
					if (!isUnselected(struct.getFeature())) {
						double tempValue = getSubtreeMaximum(struct.getFeature());
						if (struct.isMandatory() || tempValue >= 0 || isSelected(struct.getFeature())) {
							value += tempValue;
						}
					}
				}
			} else if (root.getStructure().isAlternative()) {
				List<Double> values = new ArrayList<>();
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					if (!isUnselected(struc.getFeature())) {
						if (isSelected(struc.getFeature())) {
							return value + getSubtreeMaximum(struc.getFeature());
						}
						values.add(getSubtreeMaximum(struc.getFeature()));
					}
				}
				return value + getMaxValue(values);
			}
		}
		return value;
	}

	public Object getEstimatedMaximum() {
		selectedFeatures = config.getSelectedFeatures();
		unselectedFeatures = config.getUnSelectedFeatures();
		return getSubtreeMaximum(config.getFeatureModel().getStructure().getRoot().getFeature());
	}

	private boolean isSelected(IFeature feature) {
		return selectedFeatures.contains(feature);
	}

	private boolean isUnselected(IFeature feature) {
		return unselectedFeatures.contains(feature);
	}

	/**
	 * Returns maximal value of a list of doubles
	 * 
	 * @param values list of doubles
	 * @return maximal value
	 */
	private double getMaxValue(List<Double> values) {
		double max = values.get(0);
		for (double value : values) {
			if (value > max) {
				max = value;
			}
		}
		return max;
	}

}
