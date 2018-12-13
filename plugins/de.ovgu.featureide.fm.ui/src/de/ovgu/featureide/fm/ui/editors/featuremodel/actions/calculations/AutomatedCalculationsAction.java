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

import static de.ovgu.featureide.fm.core.localization.StringTable.AUTOMATED_CALCULATIONS;

import java.util.concurrent.locks.Lock;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureStatus;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
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
		final IFeatureModel featureModel;
		final Lock lock = featureModelManager.getFileOperationLock();
		lock.lock();
		try {
			featureModel = featureModelManager.editObject();
			if (featureModel.getAnalyser().runCalculationAutomatically) {
				for (final IFeature f : featureModel.getFeatures()) {
					f.getProperty().setFeatureStatus(FeatureStatus.NORMAL, false);
				}
				for (final IConstraint c : featureModel.getConstraints()) {
					c.setConstraintAttribute(ConstraintAttribute.NORMAL, false);
				}
				featureModel.getAnalyser().runCalculationAutomatically = false;
			} else {
				featureModel.getAnalyser().runCalculationAutomatically = true;
			}
		} finally {
			lock.unlock();
		}
		featureModel.handleModelDataChanged();
	}

	@Override
	public void update() {
		setChecked(featureModelManager.editObject().getAnalyser().runCalculationAutomatically);
	}

}
