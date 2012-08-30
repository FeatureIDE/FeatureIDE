/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.AbstractOperation;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 *
 * 
 * @author Fabian Benduhn
 */
public class FeatureDeleteOperation extends AbstractOperation {

	private FeatureModel featureModel;
	private Feature feature;
	private Feature oldParent;
	private int oldIndex;
	private LinkedList<Constraint> oldConstraints;
	private LinkedList<Feature> oldChildren;
	private boolean deleted = false;
	private boolean refresh;
	private Feature replaceWithFeature;

	public FeatureDeleteOperation(FeatureModel featureModel, Feature feature, boolean refreshDiagram) 
	{
		super("Delete");
		this.featureModel = featureModel;
		this.feature = feature;
		this.refresh = refreshDiagram;
		this.replaceWithFeature = null;
	}
	
	public FeatureDeleteOperation(FeatureModel featureModel, Feature feature, boolean refreshDiagram, Feature replaceWithFeature) {
		super("Delete");
		this.featureModel = featureModel;
		this.feature = feature;
		this.refresh = refreshDiagram;
		this.replaceWithFeature = replaceWithFeature;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#execute(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus execute(IProgressMonitor arg0, IAdaptable arg1)
			throws ExecutionException {
		return redo(arg0, arg1);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#redo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus redo(IProgressMonitor arg0, IAdaptable arg1)
			throws ExecutionException {
		feature = featureModel.getFeature(feature.getName());
		oldParent = feature.getParent();
		if (oldParent != null) {
			oldIndex = oldParent.getChildIndex(feature);
		}
		oldChildren = new LinkedList<Feature>();
		oldChildren.addAll(feature.getChildren());

		if (oldParent != null) {
			oldParent = featureModel.getFeature(oldParent.getName());
		}
		LinkedList<Feature> oldChildrenCopy = new LinkedList<Feature>();

		for (Feature f : oldChildren) {
			if (!f.getName().equals(feature.getName())) {
				Feature oldChild = featureModel.getFeature(f.getName());
				oldChildrenCopy.add(oldChild);
			}
		}
		
		oldChildren = oldChildrenCopy;
		feature = featureModel.getFeature(feature.getName());
		if (feature == featureModel.getRoot()) {
			featureModel.replaceRoot(featureModel.getRoot().removeLastChild());
			deleted = true;
		} else {
			deleted = featureModel.deleteFeature(feature);
		}
		if (refresh)
			featureModel.handleModelDataLoaded();
		
		//Replace Featurename in Constraints
		if (replaceWithFeature != null)
		{
			oldConstraints = new LinkedList<Constraint>();
			for (Constraint c : featureModel.getConstraints())
			{				
				oldConstraints.add(new Constraint(featureModel, c.getNode().clone()));
				if (c.getContainedFeatures().contains(feature))
				{
					 c.getNode().replaceFeature(feature, replaceWithFeature);
				}
			}			
		}
		
		
		return Status.OK_STATUS;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.operations.AbstractOperation#undo(org.eclipse
	 * .core.runtime.IProgressMonitor, org.eclipse.core.runtime.IAdaptable)
	 */
	@Override
	public IStatus undo(IProgressMonitor arg0, IAdaptable arg1)
			throws ExecutionException {
		try {
			if (!deleted)
				return Status.OK_STATUS;
			if (oldParent != null) {
				oldParent = featureModel.getFeature(oldParent.getName());
			}
			LinkedList<Feature> oldChildrenCopy = new LinkedList<Feature>();

			for (Feature f : oldChildren)
			{
				if (!f.getName().equals(feature.getName()))
				{
					Feature child = featureModel.getFeature(f.getName());
					if (child != null && child.getParent() != null)
					{
						child.getParent().removeChild(child);
					}
					oldChildrenCopy.add(child);
				}
			}
			
			oldChildren = oldChildrenCopy;

			feature.setChildren(oldChildren);
			if (oldParent != null) {
				oldParent.addChildAtPosition(oldIndex, feature);
			} else {
				featureModel.setRoot(feature);
			}
			featureModel.addFeature(feature);
			
			//Replace Featurename in Constraints
			if (replaceWithFeature != null)
			{
				featureModel.setConstraints(oldConstraints);
			}
			
			if (refresh) {
				featureModel.handleModelDataLoaded();
				featureModel.redrawDiagram();
			}
		} catch (Exception e) {
			FMUIPlugin.getDefault().logError(e);
		}

		return Status.OK_STATUS;

	}

	@Override
	public boolean canUndo() {
		if (oldParent == null
				|| featureModel.getFeature(oldParent.getName()) != null) {
			return true;
		}
		return false;
	}
}
