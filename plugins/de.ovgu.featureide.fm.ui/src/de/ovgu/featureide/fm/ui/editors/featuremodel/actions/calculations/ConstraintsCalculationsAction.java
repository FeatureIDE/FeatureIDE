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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_CONSTRAINT_ERRORS;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AFeatureModelAction;

/**
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class ConstraintsCalculationsAction extends AFeatureModelAction {

	public static final String ID = "de.ovgu.featureide.constraintscalculations";

	public ConstraintsCalculationsAction(IFeatureModelManager featureModelManager) {
		super(CALCULATE_CONSTRAINT_ERRORS, ID, featureModelManager);
	}

	@Override
	public void run() {
		Boolean isCalculatingConstraints = FeatureModelProperty.getBooleanProperty(featureModelManager.getSnapshot().getProperty(),
				FeatureModelProperty.TYPE_CALCULATIONS, FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS);
		if (isCalculatingConstraints == null) {
			// Default value = always active
			isCalculatingConstraints = Boolean.TRUE;
		}

		// Change model property
		if (isCalculatingConstraints) {
			featureModelManager.editObject(this::setPropertyToDeactive);
		} else {
			featureModelManager.editObject(this::setPropertyToActive);
		}
		// Model data changed => reanalyze the model in the editor if needed
		featureModelManager.getVarObject().handleModelDataChanged();
	}

	/***
	 * Consumer function used to edit the current models property for automated calculation setting it to true.
	 *
	 * @param model Model that should be changed.
	 */
	private void setPropertyToActive(IFeatureModel model) {
		// Calculation of constraints requires the calculation of features
		String propertyType = FeatureModelProperty.TYPE_CALCULATIONS;
		String propertyName = FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_FEATURES;
		model.getProperty().set(propertyName, propertyType, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
		propertyType = FeatureModelProperty.TYPE_CALCULATIONS;
		propertyName = FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS;
		model.getProperty().set(propertyName, propertyType, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
	}

	/***
	 * Consumer function used to edit the current models property for automated calculation setting it to false.
	 *
	 * @param model Model that should be changed.
	 */
	private void setPropertyToDeactive(IFeatureModel model) {
		final String propertyType = FeatureModelProperty.TYPE_CALCULATIONS;
		final String propertyName = FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS;
		model.getProperty().set(propertyName, propertyType, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
	}

	@Override
	public void update() {
		Boolean isChecked = FeatureModelProperty.getBooleanProperty(featureModelManager.getSnapshot().getProperty(), FeatureModelProperty.TYPE_CALCULATIONS,
				FeatureModelProperty.PROPERTY_CALCULATIONS_CALCULATE_CONSTRAINTS);
		if (isChecked == null) {
			// Default value = always active
			isChecked = Boolean.TRUE;
		}
		setChecked(isChecked);
	}

}
