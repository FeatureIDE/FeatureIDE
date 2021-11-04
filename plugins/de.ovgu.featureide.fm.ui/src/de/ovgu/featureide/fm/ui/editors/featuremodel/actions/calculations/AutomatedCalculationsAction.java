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

import static de.ovgu.featureide.fm.core.localization.StringTable.AUTOMATED_CALCULATIONS;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelProperty;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AFeatureModelAction;

/**
 * An action to activate/deactivate automated calculations on changes to the feature model.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class AutomatedCalculationsAction extends AFeatureModelAction {

	public static final String ID = "de.ovgu.featureide.automatedcalculations";

	public AutomatedCalculationsAction(IFeatureModelManager featureModelManager) {
		super(AUTOMATED_CALCULATIONS, ID, featureModelManager);
	}

	@Override
	public void run() {
		// Check for activated automated analyses.
		Boolean isAutomaticCalculation = FeatureModelProperty.getBooleanProperty(featureModelManager.getSnapshot().getProperty(),
				FeatureModelProperty.TYPE_CALCULATIONS, FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY);
		// No property value available => take default value
		if (isAutomaticCalculation == null) {
			if (featureModelManager.getSnapshot().getNumberOfFeatures() >= FeatureModelProperty.BIG_MODEL_LIMIT) {
				// Is big model => no automatic analyses as default
				isAutomaticCalculation = Boolean.FALSE;
			} else {
				// Is small model => automatic analyses as default
				isAutomaticCalculation = Boolean.TRUE;
			}
		}

		// Clear old results from the analyses collection.
		final FeatureModelFormula variableFormula = featureModelManager.getVariableFormula();
		final FeatureModelAnalyzer analyzer = variableFormula.getAnalyzer();
		final IFeatureModel featureModel = variableFormula.getFeatureModel();
		if (isAutomaticCalculation) {
			for (final IFeature f : featureModel.getFeatures()) {
				analyzer.getFeatureProperties(f).resetStatus();
			}
			for (final IConstraint c : featureModel.getConstraints()) {
				analyzer.getConstraintProperties(c).resetStatus();
			}
		}

		// Change model property
		if (isAutomaticCalculation) {
			featureModelManager.editObject(this::setPropertyToDeactive, FeatureModelManager.CHANGE_MODEL_PROPERTY);
		} else {
			featureModelManager.editObject(this::setPropertyToActive, FeatureModelManager.CHANGE_MODEL_PROPERTY);
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
		final String propertyType = FeatureModelProperty.TYPE_CALCULATIONS;
		final String propertyName = FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY;
		model.getProperty().set(propertyName, propertyType, FeatureModelProperty.VALUE_BOOLEAN_TRUE);
	}

	/***
	 * Consumer function used to edit the current models property for automated calculation setting it to false.
	 *
	 * @param model Model that should be changed.
	 */
	private void setPropertyToDeactive(IFeatureModel model) {
		final String propertyType = FeatureModelProperty.TYPE_CALCULATIONS;
		final String propertyName = FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY;
		model.getProperty().set(propertyName, propertyType, FeatureModelProperty.VALUE_BOOLEAN_FALSE);
	}

	@Override
	public void update() {
		Boolean isChecked = FeatureModelProperty.getBooleanProperty(featureModelManager.getSnapshot().getProperty(), FeatureModelProperty.TYPE_CALCULATIONS,
				FeatureModelProperty.PROPERTY_CALCULATIONS_RUN_AUTOMATICALLY);
		if (isChecked == null) {
			if (featureModelManager.getSnapshot().getNumberOfFeatures() >= FeatureModelProperty.BIG_MODEL_LIMIT) {
				// Is big model => no automatic analyses as default
				isChecked = Boolean.FALSE;
			} else {
				// Is small model => automatic analyses as default
				isChecked = Boolean.TRUE;
			}
		}
		setChecked(isChecked);
	}

}
