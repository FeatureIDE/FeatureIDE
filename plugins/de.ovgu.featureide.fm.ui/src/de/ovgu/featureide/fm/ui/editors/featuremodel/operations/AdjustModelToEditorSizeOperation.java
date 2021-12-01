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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADJUST_MODEL_TO_EDITOR;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
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
public class AdjustModelToEditorSizeOperation extends AbstractGraphicalFeatureModelOperation {

	private final FeatureDiagramEditor editor;
	private final LinkedList<String> affectedFeatureList = new LinkedList<>();

	private boolean collapse;

	public AdjustModelToEditorSizeOperation(IGraphicalFeatureModel graphicalFeatureModel, FeatureDiagramEditor editor) {
		super(graphicalFeatureModel, ADJUST_MODEL_TO_EDITOR);
		this.editor = editor;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		// 0 is the manual layout, there is no greedy for manual layout
		if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
			return new FeatureIDEEvent(null, EventType.DEFAULT);
		}
		new CollapseAllOperation(graphicalFeatureModel, true).operation(featureModel);
		checkChildren(featureModel.getStructure().getRoot().getFeature());
		return new FeatureIDEEvent(null, EventType.FEATURE_COLLAPSED_ALL_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
			return new FeatureIDEEvent(null, EventType.DEFAULT);
		} else {
			// TODO implement reverse operation
			for (final String name : affectedFeatureList) {
				graphicalFeatureModel.getGraphicalFeature(featureModel.getFeature(name)).setCollapsed(!collapse);
			}
			return new FeatureIDEEvent(null, EventType.FEATURE_COLLAPSED_ALL_CHANGED);
		}
	}

	private void checkChildren(IFeature root) {
		final LinkedList<LinkedList<IFeature>> layers = calculateLevels(root);
		IGraphicalFeature leftestChild = null;
		for (int i = 1; i < layers.size(); i++) {
			final LinkedList<IFeature> layer = layers.get(i);
			final IGraphicalFeature left = graphicalFeatureModel.getGraphicalFeature(layer.get(0));
			final IGraphicalFeature right = graphicalFeatureModel.getGraphicalFeature(layer.getLast());

			boolean isLayerSomewhereOutOfSight = editor.getViewer().isNodeOutOfSight(left) || editor.getViewer().isNodeOutOfSight(right);
			if (isLayerSomewhereOutOfSight) {
				break;
			}
			if (left.getAllGraphicalChildren().size() > 0) {
				leftestChild = left.getAllGraphicalChildren().get(0);
			}
			for (final IFeature node : layer) {
				final IGraphicalFeature gf = graphicalFeatureModel.getGraphicalFeature(node);
				editor.getViewer().internRefresh(true);
				editor.propertyChange(new FeatureIDEEvent(null, EventType.FEATURE_COLLAPSED_ALL_CHANGED));
				if (editor.getViewer().isNodeOutOfSight(gf)) {
					gf.setCollapsed(true);
					break;
				} else {
					gf.setCollapsed(false);
					editor.propertyChange(new FeatureIDEEvent(null, EventType.FEATURE_COLLAPSED_ALL_CHANGED));
					final boolean leftestChildIsOutOfSight = leftestChild != null ? editor.getViewer().isNodeOutOfSight(leftestChild) : false;
					final int lastChildIndex = gf.getAllGraphicalChildren().size() - 1;
					final boolean rightestChildIsOutOfSight;
					if (lastChildIndex < 0) {
						rightestChildIsOutOfSight = false;
					} else {
						rightestChildIsOutOfSight = editor.getViewer().isNodeOutOfSight(gf.getAllGraphicalChildren().get(lastChildIndex));
						isLayerSomewhereOutOfSight = editor.getViewer().isNodeOutOfSight(left) || editor.getViewer().isNodeOutOfSight(right);
					}
					if (leftestChildIsOutOfSight || rightestChildIsOutOfSight || isLayerSomewhereOutOfSight) {
						gf.setCollapsed(true);
					}
				}
			}
		}
	}

	/**
	 * Calculates the levels from the given IGraphicalFeature by iterating through the levels of features.
	 *
	 * @param root of the model.
	 * @return list of levels, which are again lists of IFeatures
	 */
	private LinkedList<LinkedList<IFeature>> calculateLevels(IFeature root) {
		final LinkedList<LinkedList<IFeature>> levels = new LinkedList<>();
		LinkedList<IFeature> level = new LinkedList<>();
		level.add(root);
		while (!level.isEmpty()) {
			levels.add(level);
			final LinkedList<IFeature> newLevel = new LinkedList<>();
			for (final IFeature feature : level) {
				final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
				for (final IFeatureStructure child : graphicalFeature.getObject().getStructure().getChildren()) {
					newLevel.add(child.getFeature());
				}
			}
			level = newLevel;
		}

		return levels;
	}
}
