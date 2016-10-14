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
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.ADJUST_MODEL_TO_EDITOR;

import java.util.LinkedList;
import org.eclipse.core.commands.ExecutionException;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramEditor;

/**
 * Operation with functionality to set all features to collapsed. Enables
 * undo/redo functionality.
 * 
 * @author Joshua Sprey
 * @author Enis Belli
 * @author Maximilian Kühl
 * @author Christopher Sontag
 */
public class AdjustModelToEditorSizeOperation extends AbstractFeatureModelOperation {

	boolean collapse;
	private IFeatureModel fm;

	private LinkedList<IFeature> affectedFeatureList = new LinkedList<IFeature>();

	public AdjustModelToEditorSizeOperation(IFeatureModel featureModel, Object editor) {
		super(featureModel, ADJUST_MODEL_TO_EDITOR);
		this.fm = featureModel;
		this.editor = editor;
	}

	@Override
	protected FeatureIDEEvent operation() {
		IFeatureStructure root = fm.getStructure().getRoot();
		calculateVisibleLayer(root.getFeature());
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		for (IFeature f : affectedFeatureList) {
			f.getStructure().setCollapsed(!collapse);
		}
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);

	}

	/**
	 * Calls calculateLevels with the root and iterates then over the computed levels
	 * to determine which levels are visible. Only visible features and thus visible
	 * levels are taken into account.
	 * 
	 * @param root the root feature of the graphical feature model.
	 */
	public void calculateVisibleLayer(IFeature root) {
		FeatureDiagramEditor featureDiagramEditor = (FeatureDiagramEditor) editor;
		for (IConstraint ic : featureModel.getConstraints()) {
			ic.setCollapsed(true);
		}
		((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));

		LinkedList<LinkedList<IFeature>> levels = calculateLevels(root);
		CollapseAllOperation op = new CollapseAllOperation(featureModel, true);
		try {
			op.execute(null, null);
		} catch (ExecutionException e) {
			e.printStackTrace();
		}
		LinkedList<IFeature> lastLevel = levels.getFirst();
		for (LinkedList<IFeature> level : levels) {
			/* if the last level is not null AND the level exceeds
			 * neither the width nor the height of the editor
			 */
			if (lastLevel != null && featureDiagramEditor.isLevelSizeOverLimit()) {
				affectedFeatureList.addAll(lastLevel);
				collapseLayer(lastLevel);
				break;
			}
			lastLevel = level;

			//expand next level
			for (IFeature f : level) {
				f.getStructure().setCollapsed(false);
			}
			((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
			((FeatureDiagramEditor) getEditor()).internRefresh(true);
		}
		
		LinkedList<IFeature> lastStep = lastLevel;
		do{
			lastStep = calculateNextLevel(lastStep);
		} while (lastStep != null && lastStep.size() != 0);
		
		for (IConstraint ic : featureModel.getConstraints()) {
			ic.setCollapsed(false);
		}
		((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
	}

	public LinkedList<IFeature> calculateNextLevel(LinkedList<IFeature> lastLevel)
	{
		FeatureDiagramEditor featureDiagramEditor = (FeatureDiagramEditor)getEditor();
		
		LinkedList<IFeature> parents = new LinkedList<IFeature>();
		for(IFeature f : lastLevel)
		{
			if(f.getStructure().hasChildren())
			{
				parents.add(f);
			}
		}
		if(parents.size() == 0)
		{
			return null;
		}
		LinkedList<IFeature> bestSolution = new LinkedList<IFeature>();
		for(LinkedList<IFeature> parentSet : powerSet(parents))
		{
			LinkedList<IFeature> childList = new LinkedList<IFeature>();
			for(IFeature f : parentSet)
			{
				//Expand and relayout parent
				f.getStructure().setCollapsed(false);
				((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
				((FeatureDiagramEditor) getEditor()).internRefresh(true);
				
				for(IFeatureStructure child : f.getStructure().getChildren())
				{
					childList.add(child.getFeature());
				}
			}

//			FMUIPlugin.getDefault().logInfo(parentSet.toString() + "\n" + childList.toString() + ": " + childList.size()  + "\n" + featureDiagramEditor.isLevelSizeOverLimit(childList)+ "\n" + bestSolution.toString());
			if (childList.size() != 0 && !featureDiagramEditor.isLevelSizeOverLimit()) {
				if (childList.size() > bestSolution.size()) {
					bestSolution = childList;
				}
			}
			
			for(IFeature f : parentSet)
			{				
				//collapse and relayout parent
				f.getStructure().setCollapsed(true);
			}
		}

		if (bestSolution.size() > 0) {
			for(IFeature f : bestSolution)
			{
				f.getStructure().getParent().setCollapsed(false);
			}
		}
		((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
		((FeatureDiagramEditor) getEditor()).internRefresh(true);
		return bestSolution;
//		LinkedList<IFeature> maxChilds = new LinkedList<IFeature>();
//		for (IFeature f : lastLevel) {
//			//Expand and relayout parent
//			f.getStructure().setCollapsed(false);
//			((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
//			((FeatureDiagramEditor) getEditor()).internRefresh(true);
//
//			LinkedList<IFeature> testChild = new LinkedList<IFeature>();
//			for (IFeatureStructure child : f.getStructure().getChildren()) {
//				testChild.add(child.getFeature());
//			}
//			if (testChild.size() != 0 && !featureDiagramEditor.isLevelSizeOverLimit(testChild)) {
//				if (testChild.size() >= maxChilds.size()) {
//					maxChilds = testChild;
//				}
//			}
//			//collapse and relayout parent
//			f.getStructure().setCollapsed(true);
//			((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
//			((FeatureDiagramEditor) getEditor()).internRefresh(true);
//		}
//
//		if (maxChilds.size() > 0) {
//			maxChilds.get(0).getStructure().getParent().setCollapsed(false);
//			((FeatureDiagramEditor) getEditor()).propertyChange(new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED));
//			((FeatureDiagramEditor) getEditor()).internRefresh(true);
//		}

	}
	
	public static <IFeatue> LinkedList<LinkedList<IFeatue>> powerSet(LinkedList<IFeatue> originalSet) {
		LinkedList<LinkedList<IFeatue>> sets = new LinkedList<LinkedList<IFeatue>>();
		if (originalSet.isEmpty()) {
			sets.add(new LinkedList<IFeatue>());
			return sets;
		}
		LinkedList<IFeatue> list = new LinkedList<IFeatue>(originalSet);
		IFeatue head = list.get(0);
		LinkedList<IFeatue> rest = new LinkedList<IFeatue>(list.subList(1, list.size()));
		for (LinkedList<IFeatue> set : powerSet(rest)) {
			LinkedList<IFeatue> newSet = new LinkedList<IFeatue>();
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
		for (IFeature feature : level) {
			feature.getStructure().setCollapsed(true);
		}
	}

	/**
	 * Calculates the levels from the given IGraphicalFeature by iterating through the levels
	 * of features.
	 * 
	 * @param root root of the model.
	 * @return list of levels, which are again lists of IFeatures
	 */
	private LinkedList<LinkedList<IFeature>> calculateLevels(IFeature root) {
		LinkedList<LinkedList<IFeature>> levels = new LinkedList<LinkedList<IFeature>>();
		LinkedList<IFeature> level = new LinkedList<IFeature>();
		level.add(root);
		while (!level.isEmpty()) {
			levels.add(level);
			LinkedList<IFeature> newLevel = new LinkedList<IFeature>();
			for (IFeature feature : level) {
				for (IFeatureStructure child : feature.getStructure().getChildren()) {
					newLevel.add(child.getFeature());
				}
			}
			level = newLevel;
		}

		return levels;
	}
}