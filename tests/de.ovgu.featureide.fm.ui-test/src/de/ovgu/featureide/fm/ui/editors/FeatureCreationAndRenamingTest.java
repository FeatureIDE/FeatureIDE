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

import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.Feature;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.elements.GraphicalFeatureModel;

/**
 * This class tests that in a feature model, new features can be created above, below existing features or as siblings, and that they can be renamed right after
 * their creation.
 *
 * @author Jedelhauser Kevin
 * @author Jutz Benedikt
 */
public class FeatureCreationAndRenamingTest {

	/**
	 * The feature model to edit.
	 */
	private FeatureModelManager testModelManager;
	/**
	 * The feature diagram editor.
	 */
	private FeatureDiagramEditor editor;

	/**
	 * Load the feature model under "./testFeatureModels/basic.xml", and create a new {@link FeatureDiagramEditor} to display it in.
	 */
	@Before
	public void loadBasicModel() {
		testModelManager = Commons.loadTestFeatureModelFromFile("basic.xml");
		final IGraphicalFeatureModel gfm = new GraphicalFeatureModel(testModelManager);
		gfm.init();
		editor = new FeatureDiagramEditor(testModelManager, gfm, true);
		editor.setFocus();
	}

	/**
	 * Test the creation of new features: <ol> <li>Select the feature named "A", and create a feature below named "C".</li> <li>Select the new feature "C", and
	 * create a sibling feature named "D".</li> <li>Select feature "B", and create a feature above named "E".</li> </ol>
	 */
	@Test
	public void testCreationMethods() {
		// Get the graphical model.
		final IGraphicalFeatureModel graphicalModel = editor.getGraphicalFeatureModel();

		// In the editor, select the feature called "A".
		final IFeatureModel model = (IFeatureModel) editor.getFeatureModel().getObject();
		final IFeature aFeature = model.getFeature("A");

		// Create a new FeatureIDEEvent that adds a new feature to the parent
		// feature "A" for the given feature model. Add the feature "C" below it.
		final IFeature cFeature = new Feature(model, "C");
		editor.propertyChange(new FeatureIDEEvent(model, EventType.FEATURE_ADD, aFeature, cFeature));
		// Assert that "C" exists and has "A" as parent.
		final IGraphicalFeature cGraphicalFeature = graphicalModel.getGraphicalFeature(cFeature);
		assertNotNull(cGraphicalFeature);
		assertTrue(graphicalModel.getGraphicalFeature(aFeature).getGraphicalChildren().contains(cGraphicalFeature));
	}
}
