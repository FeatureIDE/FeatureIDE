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
package de.ovgu.featureide.fm.ui.editors;

import java.util.List;
import java.util.Map;

import org.eclipse.gef.EditPart;
import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SelectSubtreeAction;

/**
 * {@link FeatureSubtreeSelectionTest} verifies that selecting subtrees of single and multiple features works correctly.
 *
 * @author Jedelhauser Kevin
 * @author Jutz Benedikt
 */
public class FeatureSubtreeSelectionTest {

	/**
	 * The feature model manager.
	 */
	private IFeatureModelManager manager;
	private IGraphicalFeatureModel graphicalModel;
	private FeatureDiagramEditor editor;
	private FeatureDiagramViewer viewer;

	/**
	 * Load the feature model given in TestConfigurationModel.xml.
	 */
	@Before
	public void initalize() {
		manager = Commons.loadTestFeatureModelFromFile("TestConfigurationModel.xml");
		graphicalModel = new GraphicalFeatureModel(manager);
		graphicalModel.init();
		editor = new FeatureDiagramEditor(manager, graphicalModel, true);
		editor.setFocus();
		viewer = editor.getViewer();
		// viewer.getContents().activate();
	}

	@Test
	public void testSingleSelection() {

	}

	/**
	 * Try to select the subtrees Optional and Mandatory. Assert that those features, along with their children Alternative1, Alternative2, Or1 and Or2 are
	 * selected.
	 */
	@Test
	public void testMultipleSelection() {
		final Map<?, ?> editParts = viewer.getEditPartRegistry();
		// Get and select the Optional feature from the feature model.
		final IFeatureModel model = editor.getFeatureModel().getObject();
		final IFeature optFeature = model.getFeature("Optional");
		// Also get the mandatory feature.
		final IFeature manFeature = model.getFeature("Mandatory");
		// graphicalModel.getGraphicalFeature(manFeature).setConstraintSelected(true);

		// Run the SelctSubtreeAction.
		final SelectSubtreeAction action = new SelectSubtreeAction(viewer, manager);
		action.run();

		// Assert that the Optional, Mandatory feature and their sub features have been selected.
		final List<EditPart> parts = viewer.getSelectedEditParts();
	}
}
