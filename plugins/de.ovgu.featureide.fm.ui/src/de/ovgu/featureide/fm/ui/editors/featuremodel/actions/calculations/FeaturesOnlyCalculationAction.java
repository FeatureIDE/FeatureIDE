/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import de.ovgu.featureide.fm.core.ProjectManager;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * Action to specify feature model analysis.<br>
 * Only features will be analyzed and not constraints.
 * 
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class FeaturesOnlyCalculationAction extends Action {

	private final IFeatureModel featureModel;

	public FeaturesOnlyCalculationAction(GraphicalViewerImpl viewer, IFeatureModel featureModel) {
		super(CALCULATE_FEATURES);
		this.featureModel = featureModel;
		setToolTipText("Test");
		setChecked(ProjectManager.getAnalyzer(featureModel).calculateFeatures);
	}

	@Override
	public void run() {
		if (ProjectManager.getAnalyzer(featureModel).calculateFeatures) {
			ProjectManager.getAnalyzer(featureModel).calculateFeatures = false;
			ProjectManager.getAnalyzer(featureModel).calculateConstraints = false;
			ProjectManager.getAnalyzer(featureModel).calculateRedundantConstraints = false;
			ProjectManager.getAnalyzer(featureModel).calculateTautologyConstraints = false;
			ProjectManager.getAnalyzer(featureModel).calculateDeadConstraints = false;
			ProjectManager.getAnalyzer(featureModel).calculateFOConstraints = false;
		} else {
			ProjectManager.getAnalyzer(featureModel).calculateFeatures = true;
			ProjectManager.getAnalyzer(featureModel).calculateDeadConstraints = true;
			ProjectManager.getAnalyzer(featureModel).calculateFOConstraints = true;
		}
		featureModel.handleModelDataChanged();
	}

}
