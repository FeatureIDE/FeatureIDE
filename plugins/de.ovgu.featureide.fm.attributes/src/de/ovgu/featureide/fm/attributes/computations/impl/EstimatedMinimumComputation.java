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
 * Estimates the minimum of a numerical attribute given a partial configuration Only supposed to be used on numerical attributes
 * 
 * @author Chico Sundermann
 */
public class EstimatedMinimumComputation {

	Configuration config;
	IFeatureAttribute attribute;
	List<IFeature> selectedFeatures;
	List<IFeature> unselectedFeatures;

	public EstimatedMinimumComputation(Configuration config, IFeatureAttribute attribute) {
		this.config = config;
		this.attribute = attribute;
	}

	/**
	 * Estimates the minimum of the value sum regarding a partial configuration
	 * 
	 * @return Minimum
	 */
	public Object getEstimatedMinimum() {
		selectedFeatures = config.getSelectedFeatures();
		unselectedFeatures = config.getUnSelectedFeatures();
		return getSubtreeMinimum(config.getFeatureModel().getStructure().getRoot().getFeature());
	}

	private double getSubtreeMinimum(IFeature root) {
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
			if (root.getStructure().isAnd()) {
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					double tempValue = getSubtreeMinimum(struc.getFeature());
					if (struc.isMandatory() || isSelected(struc.getFeature()) || (tempValue < 0 && !isUnselected(struc.getFeature()))) {
						value += getSubtreeMinimum(struc.getFeature());
					}
				}

			} else if (root.getStructure().isAlternative()) {
				List<Double> values = new ArrayList<>();
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					if (isSelected(struc.getFeature())) {
						return value + getSubtreeMinimum(struc.getFeature());
					}
					if (!isUnselected(struc.getFeature())) {
						values.add(getSubtreeMinimum(struc.getFeature()));
					}
				}
				return value + getMinValue(values);
			} else if (root.getStructure().isOr()) {
				List<Double> values = new ArrayList<>();
				int unselectedCount = 0;
				for (IFeatureStructure struc : root.getStructure().getChildren()) {
					if (isUnselected(struc.getFeature())) {
						unselectedCount++;
					} else {
						double tempValue = getSubtreeMinimum(struc.getFeature());
						if (isSelected(struc.getFeature()) || tempValue < 0) {
							value += tempValue;
						} else {
							values.add(tempValue);
						}
					}
				}
				if (values.size() + unselectedCount == root.getStructure().getChildrenCount()) {
					return value + getMinValue(values);
				}
			}
		}
		return value;
	}

	private boolean isSelected(IFeature feature) {
		return selectedFeatures.contains(feature);
	}

	private boolean isUnselected(IFeature feature) {
		return unselectedFeatures.contains(feature);
	}

	private double getMinValue(List<Double> values) {
		double min = values.get(0);
		for (double temp : values) {
			if (temp < min) {
				min = temp;
			}
		}
		return min;
	}

}
