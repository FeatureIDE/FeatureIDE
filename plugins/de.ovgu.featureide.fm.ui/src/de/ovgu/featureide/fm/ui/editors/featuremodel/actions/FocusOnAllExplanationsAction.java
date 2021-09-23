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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.gef.EditPart;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.explanations.fm.MultipleAnomaliesExplanation;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramViewer;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnExplanationOperation;

/**
 * Action that calculates all explanations and marks all relevant features.
 *
 * @author Benedikt Jutz
 */
public class FocusOnAllExplanationsAction extends Action {

	/**
	 * The ID of this action.
	 */
	public static final String ID = "de.ovgu.featureide.focusonallexplanations";

	/**
	 * The graphical feature model.
	 */
	private final FeatureDiagramViewer viewer;

	/**
	 * Creates a new {@link FocusOnAllExplanationsAction}.
	 *
	 * @param viewer - {@link FeatureDiagramViewer}
	 */
	public FocusOnAllExplanationsAction(FeatureDiagramViewer viewer) {
		super(StringTable.FOCUS_ON_ALL_EXPLANATIONS);
		setId(ID);
		this.viewer = viewer;
	}

	/**
	 * Creates or loads a previously saved full explanation for all feature models, then focuses on its elements. Select the feature diagram root to sho the
	 * explanations.
	 */
	@Override
	public void run() {
		final IGraphicalFeatureModel gfm = viewer.getGraphicalFeatureModel();
		final IFeatureModel featureModel = gfm.getFeatureModelManager().getVarObject();

		final FeatureModelAnalyzer analyzer = FeatureModelManager.getInstance(featureModel).getVariableFormula().getAnalyzer();
		final MultipleAnomaliesExplanation explanation = analyzer.getMultipleAnomaliesExplanation();
		FeatureModelOperationWrapper.run(new FocusOnExplanationOperation(gfm, explanation));

		final IFeature root = featureModel.getStructure().getRoot().getFeature();
		final FeatureEditPart rootPart = (FeatureEditPart) viewer.getEditPartRegistry().get(gfm.getGraphicalFeature(root));

		viewer.getSelectionManager().deselectAll();
		rootPart.setSelected(EditPart.SELECTED_PRIMARY);
		viewer.getSelectionManager().appendSelection(rootPart);
		featureModel.fireEvent(FeatureIDEEvent.getDefault(EventType.REDRAW_DIAGRAM));
	}
}
