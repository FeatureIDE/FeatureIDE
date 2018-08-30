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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADJUST_MODEL_TO_EDITOR;

import java.util.ArrayList;
import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to set all features to collapsed. Enables undo/redo functionality.
 *
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Maximilian Kühl
 * @author Christopher Sontag
 */
public class AdjustModelToEditorSizeOperation extends AbstractFeatureModelOperation {

	boolean collapse;
	private final IFeatureModel featureModel;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final LinkedList<IFeature> affectedFeatureList = new LinkedList<IFeature>();

	public AdjustModelToEditorSizeOperation(IGraphicalFeatureModel graphicalFeatureModel, Object editor) {
		super(graphicalFeatureModel.getFeatureModel(), ADJUST_MODEL_TO_EDITOR);
		featureModel = graphicalFeatureModel.getFeatureModel();
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.editor = editor;
	}

	@Override
	protected FeatureIDEEvent operation() {
		// 0 is the manual layout, there is no greedy for manual layout
		if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
			return new FeatureIDEEvent(null, EventType.DEFAULT);
		}
		getVisibleFeatures();
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
			return new FeatureIDEEvent(null, EventType.DEFAULT);
		}
		for (final IFeature f : affectedFeatureList) {
			final IGraphicalFeature graphicalF = graphicalFeatureModel.getGraphicalFeature(f);
			graphicalF.setCollapsed(!collapse);
		}
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);

	}

	private IGraphicalFeature findRoot(ArrayList<IGraphicalFeature> tree) {
		for (final IGraphicalFeature feature : tree) {
			if (feature.getSourceConnection().getTarget() == null) {
				return feature;
			}
		}
		return null;
	}

	private void checkChildren(IGraphicalFeature root) {

		final ArrayList<IGraphicalFeature> childern = new ArrayList<IGraphicalFeature>(root.getGraphicalChildren(false));
		final FeatureDiagramEditor featureDiagramEditor = (FeatureDiagramEditor) editor;
		if (childern.size() > 0) {
			collapseLayer(childern, true);
			root.setCollapsed(false);

		}
		featureDiagramEditor.getViewer().internRefresh(true);
		for (int j = 0; j < childern.size(); j++) {
			if (featureDiagramEditor.getViewer().isNodeOutOfSight(childern.get(j))) {
				root.setCollapsed(true);
				break;
			} else {
				checkChildren(childern.get(j));
			}
		}

	}

	private void getVisibleFeatures() {
		final IGraphicalFeature root = graphicalFeatureModel.getGraphicalFeature(featureModel.getStructure().getRoot().getFeature());
		checkChildren(root);
	}

	/**
	 * Collapses all features of the given list of features.
	 *
	 * @param level list of features
	 */
	private void collapseLayer(ArrayList<IGraphicalFeature> level, boolean collapsed) {
		for (final IGraphicalFeature graphicalFeature : level) {

			graphicalFeature.setCollapsed(collapsed);
		}
	}

	@Override
	public FeatureDiagramEditor getEditor() {
		return (FeatureDiagramEditor) super.getEditor();
	}
}
