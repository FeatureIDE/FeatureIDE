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
package de.ovgu.featureide.fm.core.base.impl;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelProperty;
import de.ovgu.featureide.fm.core.base.IPropertyContainer;

/**
 * All additional properties of one {@link IFeature} instance.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public class FeatureModelProperty extends MapPropertyContainer implements IFeatureModelProperty {

	public static final String VALUE_BOOLEAN_TRUE = "true";
	public static final String VALUE_BOOLEAN_FALSE = "false";
	/** The big model size limit changes the behaviour of FeatureIDE (e.g., "analyses are no longer performed automatically as default") */
	public static int BIG_MODEL_LIMIT = 1000;
	public static String TYPE_CALCULATIONS = "calculations";
	/** Property decides whether calculations are performed automatically. */
	public static String PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY = "runcalculationsautomatically";
	/** Property decides whether calculations for feature are performed. */
	public static String PROPERTY_CALCULATIONS_CALCULATE_FEATURES = "calculatefeatures";
	/** Property decides whether calculations for constraints are performed. */
	public static String PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS = "calculateconstraints";

	@Override
	public int hashCode() {
		return super.hashCode() * Objects.hash(featureOrderInXML, annotations, comments);
	}

	@Override
	public boolean equals(Object obj) {
		if (super.equals(obj)) {
			final FeatureModelProperty other = (FeatureModelProperty) obj;
			return (featureOrderInXML == other.featureOrderInXML) && Objects.equals(annotations, other.annotations) && Objects.equals(comments, other.comments);
		} else {
			return false;
		}
	}

	/**
	 * Saves the annotations from the model file as they were read, because they were not yet used.
	 */
	protected final List<String> annotations;

	/**
	 * All comment lines from the model file without line number at which they occur
	 */
	protected final List<String> comments;

	protected final IFeatureModel correspondingFeatureModel;

	protected boolean featureOrderInXML;

	protected FeatureModelProperty(FeatureModelProperty oldProperty, IFeatureModel correspondingFeatureModel) {
		super(oldProperty);
		this.correspondingFeatureModel = correspondingFeatureModel != null ? correspondingFeatureModel : oldProperty.correspondingFeatureModel;

		featureOrderInXML = oldProperty.featureOrderInXML;

		comments = new LinkedList<>(oldProperty.comments);
		annotations = new LinkedList<>(oldProperty.annotations);
	}

	public FeatureModelProperty(IFeatureModel correspondingFeatureModel) {
		super();
		this.correspondingFeatureModel = correspondingFeatureModel;

		featureOrderInXML = false;

		comments = new LinkedList<>();
		annotations = new LinkedList<>();
	}

	@Override
	public void addAnnotation(CharSequence annotation) {
		annotations.add(annotation.toString());

	}

	@Override
	public void addComment(CharSequence comment) {
		comments.add(comment.toString());
	}

	@Override
	public IFeatureModelProperty clone(IFeatureModel newFeatureNodel) {
		return new FeatureModelProperty(this, newFeatureNodel);
	}

	@Override
	public Collection<String> getAnnotations() {
		return annotations;
	}

	@Override
	public Collection<String> getComments() {
		return comments;
	}

	@Override
	public IFeatureModel getFeatureModel() {
		return correspondingFeatureModel;
	}

	@Override
	public boolean isFeatureOrderInXML() {
		return featureOrderInXML;
	}

	@Override
	public void reset() {
		featureOrderInXML = false;
		comments.clear();
		annotations.clear();
		properties.clear();
	}

	@Override
	public void setFeatureOrderInXML(boolean featureOrderInXML) {
		this.featureOrderInXML = featureOrderInXML;
	}

	public static Boolean getBooleanProperty(IPropertyContainer properties, String propertyType, String name) {
		final String value;
		try {
			value = properties.get(name, propertyType);
		} catch (final IPropertyContainer.NoSuchPropertyException e) {
			return null;
		}
		switch (value) {
		case VALUE_BOOLEAN_FALSE:
			return false;
		case VALUE_BOOLEAN_TRUE:
			return true;
		default:
			return null;
		}
	}

	/**
	 * Indicates whether a feature diagram editor and constraint editor should perform analyses automatically based on the users preferences and model size.
	 *
	 * @param fm The relative feature model.
	 * @return true, when analyses should be performed automatically, false otherwise.
	 */
	public static boolean isRunCalculationAutomatically(IFeatureModel fm) {
		Boolean isRunAutomatically =
			getBooleanProperty(fm.getProperty(), FeatureModelProperty.TYPE_CALCULATIONS, FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY);
		if (isRunAutomatically == null) {
			if (fm.getNumberOfFeatures() >= FeatureModelProperty.BIG_MODEL_LIMIT) {
				// Is big model => no automatic analyses as default
				isRunAutomatically = Boolean.FALSE;
			} else {
				// Is small model => automatic analyses as default
				isRunAutomatically = Boolean.TRUE;
			}
		}
		return isRunAutomatically;
	}

	/**
	 * Defines whether features should be included into calculations. If features are not analyzed, then constraints are also NOT analyzed.
	 *
	 * @param fm The relative feature model.
	 * @return true, when feature should be considered when anayses are performed, false otherwise.
	 */
	public static boolean isCalculateFeatures(IFeatureModel fm) {
		Boolean isCalculatingFeatures = FeatureModelProperty.getBooleanProperty(fm.getProperty(), FeatureModelProperty.TYPE_CALCULATIONS,
				FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_FEATURES);
		if (isCalculatingFeatures == null) {
			// default value == true
			isCalculatingFeatures = Boolean.TRUE;
		}
		return isCalculatingFeatures;
	}

	/**
	 * Defines whether constraints should be included into calculations.
	 *
	 * @param fm The relative feature model.
	 * @return true, when constraints should be considered when anayses are performed, false otherwise.
	 */
	public static boolean isCalculateConstraints(IFeatureModel fm) {
		Boolean isCalculatingConstraints = FeatureModelProperty.getBooleanProperty(fm.getProperty(), FeatureModelProperty.TYPE_CALCULATIONS,
				FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS);
		if (isCalculatingConstraints == null) {
			// default value == true
			isCalculatingConstraints = Boolean.TRUE;
		}
		return isCalculatingConstraints;
	}

}
