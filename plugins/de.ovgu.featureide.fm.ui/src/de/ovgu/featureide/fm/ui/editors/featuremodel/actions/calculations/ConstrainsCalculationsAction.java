/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.concurrent.locks.Lock;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AFeatureModelAction;

/**
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class ConstrainsCalculationsAction extends AFeatureModelAction {

	public static final String ID = "de.ovgu.featureide.constraintscalculations";

	public ConstrainsCalculationsAction(IFeatureModelManager featureModelManager) {
		super(CALCULATE_CONSTRAINT_ERRORS, ID, featureModelManager);
	}

	@Override
	public void run() {
		final IFeatureModel featureModel;
		final Lock lock = featureModelManager.getFileOperationLock();
		lock.lock();
		try {
			final FeatureModelFormula variableFormula = featureModelManager.getVariableFormula();
			final FeatureModelAnalyzer analyzer = variableFormula.getAnalyzer();
			featureModel = variableFormula.getFeatureModel();
			if (analyzer.getAnalysesCollection().isCalculateConstraints()) {
				analyzer.getAnalysesCollection().setCalculateConstraints(false);
				analyzer.getAnalysesCollection().setCalculateRedundantConstraints(false);
				analyzer.getAnalysesCollection().setCalculateTautologyConstraints(false);
			} else {
				analyzer.getAnalysesCollection().setCalculateConstraints(true);
				analyzer.getAnalysesCollection().setCalculateFeatures(true);
				analyzer.getAnalysesCollection().setCalculateRedundantConstraints(true);
				analyzer.getAnalysesCollection().setCalculateTautologyConstraints(true);
				analyzer.getAnalysesCollection().setCalculateDeadConstraints(true);
				analyzer.getAnalysesCollection().setCalculateFOConstraints(true);
			}
		} finally {
			lock.unlock();
		}
		featureModel.handleModelDataChanged();
	}

	@Override
	public void update() {
		setChecked(featureModelManager.getVariableFormula().getAnalyzer().getAnalysesCollection().isCalculateConstraints());
	}

}
