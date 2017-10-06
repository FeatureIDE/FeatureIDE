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

import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;

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
public class AdjustModelToEditorSizeOperation extends AbstractFeatureModelOperation {

	boolean collapse;
	private final IFeatureModel fm;
	private final IGraphicalFeatureModel graphicalFeatureModel;

	private final LinkedList<IFeature> affectedFeatureList = new LinkedList<IFeature>();

	public AdjustModelToEditorSizeOperation(IGraphicalFeatureModel graphicalFeatureModel, Object editor) {
		super(graphicalFeatureModel.getFeatureModel(), ADJUST_MODEL_TO_EDITOR);
		fm = graphicalFeatureModel.getFeatureModel();
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.editor = editor;
	}

	@Override
	protected FeatureIDEEvent operation() {
		// 0 is the manual layout, there is no greedy for manual layout
		if (graphicalFeatureModel.getLayout().getLayoutAlgorithm() == 0) {
			return new FeatureIDEEvent(null, EventType.DEFAULT);
		}
		final IFeatureStructure root = fm.getStructure().getRoot();
		calculateVisibleLayer(root.getFeature());
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

	/**
	 * Calls calculateLevels with the root and iterates then over the computed levels to determine which levels are visible. Only visible features and thus
	 * visible levels are taken into account.
	 *
	 * @param root the root feature of the graphical feature model.
	 */
	private void calculateVisibleLayer(IFeature root) {
		final FeatureDiagramEditor featureDiagramEditor = (FeatureDiagramEditor) editor;
		getEditor().propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));

		final LinkedList<LinkedList<IFeature>> levels = calculateLevels(root);
		final CollapseAllOperation op = new CollapseAllOperation(graphicalFeatureModel, true);
		try {
			op.execute(null, null);
		} catch (final ExecutionException e) {
			e.printStackTrace();
		}
		LinkedList<IFeature> lastLevel = levels.getFirst();
		for (final LinkedList<IFeature> level : levels) {
			/*
			 * if the last level is not null AND the level exceeds neither the width nor the height of the editor
			 */
			if ((lastLevel != null) && featureDiagramEditor.getViewer().isLevelSizeOverLimit()) {
				affectedFeatureList.addAll(lastLevel);
				collapseLayer(lastLevel);
				break;
			}
			lastLevel = level;

			// expand next level
			for (final IFeature f : level) {
				final IGraphicalFeature graphicalF = graphicalFeatureModel.getGraphicalFeature(f);
				graphicalF.setCollapsed(false);
			}
			getEditor().propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
			getEditor().getViewer().internRefresh(true);
		}

		LinkedList<IFeature> lastStep = lastLevel;
		do {
			lastStep = calculateNextLevel(lastStep);
		} while ((lastStep != null) && (lastStep.size() != 0));
		getEditor().propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
	}

	private LinkedList<IFeature> calculateNextLevel(LinkedList<IFeature> lastLevel) {
		final FeatureDiagramEditor featureDiagramEditor = getEditor();

		final LinkedList<IFeature> parents = new LinkedList<IFeature>();
		for (final IFeature f : lastLevel) {
			if (f.getStructure().getChildrenCount() > 0) {
				parents.add(f);
			}
		}
		if (parents.size() == 0) {
			return null;
		}
		LinkedList<IFeature> bestSolution = new LinkedList<IFeature>();
		for (final LinkedList<IFeature> parentSet : powerSet(parents)) {
			final LinkedList<IFeature> childList = new LinkedList<IFeature>();
			for (final IFeature f : parentSet) {
				// Expand and relayout parent
				final IGraphicalFeature graphicalF = graphicalFeatureModel.getGraphicalFeature(f);
				graphicalF.setCollapsed(false);
				getEditor().propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
				getEditor().getViewer().internRefresh(true);

				for (final IGraphicalFeature child : graphicalF.getGraphicalChildren(graphicalFeatureModel.getLayout().showHiddenFeatures())) {
					childList.add(child.getObject());
				}
			}

			if ((childList.size() != 0) && !featureDiagramEditor.getViewer().isLevelSizeOverLimit()) {
				if (childList.size() > bestSolution.size()) {
					bestSolution = childList;
				}
			}

			for (final IFeature f : parentSet) {
				// collapse and relayout parent
				final IGraphicalFeature graphicalF = graphicalFeatureModel.getGraphicalFeature(f);
				graphicalF.setCollapsed(true);
			}
		}

		if (bestSolution.size() > 0) {
			for (final IFeature f : bestSolution) {
				final IGraphicalFeature graphicalFParent = graphicalFeatureModel.getGraphicalFeature(f.getStructure().getParent().getFeature());
				graphicalFParent.setCollapsed(false);
			}
		}
		getEditor().propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
		getEditor().getViewer().internRefresh(true);
		return bestSolution;
	}

	public static <IFeatue> LinkedList<LinkedList<IFeatue>> powerSet(LinkedList<IFeatue> originalSet) {
		final LinkedList<LinkedList<IFeatue>> sets = new LinkedList<LinkedList<IFeatue>>();
		if (originalSet.isEmpty()) {
			sets.add(new LinkedList<IFeatue>());
			return sets;
		}
		final LinkedList<IFeatue> list = new LinkedList<IFeatue>(originalSet);
		final IFeatue head = list.get(0);
		final LinkedList<IFeatue> rest = new LinkedList<IFeatue>(list.subList(1, list.size()));
		for (final LinkedList<IFeatue> set : powerSet(rest)) {
			final LinkedList<IFeatue> newSet = new LinkedList<IFeatue>();
			newSet.add(head);
			newSet.addAll(set);
			sets.add(newSet);
			sets.add(set);
		}
		return sets;
	}

	/**
	 * Collapses all features of the given list of features.
	 *
	 * @param level list of features
	 */
	private void collapseLayer(LinkedList<IFeature> level) {
		for (final IFeature feature : level) {
			final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(feature);
			graphicalFeature.setCollapsed(true);
		}
	}

	/**
	 * Calculates the levels from the given IGraphicalFeature by iterating through the levels of features.
	 *
	 * @param root of the model.
	 * @return list of levels, which are again lists of IFeatures
	 */
	private LinkedList<LinkedList<IFeature>> calculateLevels(IFeature root) {
		final LinkedList<LinkedList<IFeature>> levels = new LinkedList<LinkedList<IFeature>>();
		LinkedList<IFeature> level = new LinkedList<IFeature>();
		level.add(root);
		while (!level.isEmpty()) {
			levels.add(level);
			final LinkedList<IFeature> newLevel = new LinkedList<IFeature>();
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

	@Override
	public FeatureDiagramEditor getEditor() {
		return (FeatureDiagramEditor) super.getEditor();
	}
}
