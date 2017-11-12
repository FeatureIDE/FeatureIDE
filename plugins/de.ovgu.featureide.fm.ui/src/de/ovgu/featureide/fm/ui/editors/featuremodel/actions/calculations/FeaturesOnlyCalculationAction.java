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

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE_FEATURES;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Action to specify feature model analysis.<br> Only features will be analyzed and not constraints.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class FeaturesOnlyCalculationAction extends Action {

	public static final String ID = "de.ovgu.featureide.featuresonlycalculations";

	private final IFeatureModel featureModel;

	public FeaturesOnlyCalculationAction(GraphicalViewerImpl viewer, IFeatureModel featureModel) {
		super(CALCULATE_FEATURES);
		this.featureModel = featureModel;
		setToolTipText("Test");
		setChecked(featureModel.getAnalyser().calculateFeatures);
		setId(ID);
	}

	@Override
	public void run() {
		if (featureModel.getAnalyser().calculateFeatures) {
			featureModel.getAnalyser().calculateFeatures = false;
			featureModel.getAnalyser().calculateConstraints = false;
			featureModel.getAnalyser().calculateRedundantConstraints = false;
			featureModel.getAnalyser().calculateTautologyConstraints = false;
			featureModel.getAnalyser().calculateDeadConstraints = false;
			featureModel.getAnalyser().calculateFOConstraints = false;
		} else {
			featureModel.getAnalyser().calculateFeatures = true;
			featureModel.getAnalyser().calculateDeadConstraints = true;
			featureModel.getAnalyser().calculateFOConstraints = true;
		}
		featureModel.handleModelDataChanged();
	}

}
