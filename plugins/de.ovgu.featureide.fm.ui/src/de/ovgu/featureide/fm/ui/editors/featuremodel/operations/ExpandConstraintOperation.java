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

import static de.ovgu.featureide.fm.core.localization.StringTable.EXPAND_CONSTRAINT;

import java.util.LinkedList;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Operation with functionality to expand only features of this constraint. Enables undo/redo
 * functionality. Enables undo/redo functionality.
 * 
 * @author Maximilian Kühl
 * @author Christopher Sontag
 */
public class ExpandConstraintOperation extends AbstractFeatureModelOperation {

	private IConstraint iConstraint;

	private LinkedList<IFeature> affectedFeatureList = new LinkedList<IFeature>();
	
	/**
	 * @param featureModel
	 * @param label
	 */
	public ExpandConstraintOperation(IFeatureModel featureModel, IConstraint iConstraint) {
		super(featureModel, EXPAND_CONSTRAINT);
		this.iConstraint = iConstraint;
	}
	
	public void expandParents(IFeature feature) {
		if (feature.getStructure().isRoot()) {
			return;
		}
		
		IFeatureStructure p = feature.getStructure().getParent();
		while (!p.isRoot()) {
			if (p.isCollapsed()) {
				expandFeature(p);
			} 
			p = p.getParent();
		}
		p.setCollapsed(false);
		featureModel.fireEvent(new FeatureIDEEvent(p.getFeature(), EventType.COLLAPSED_CHANGED));
	}

	@Override
	protected FeatureIDEEvent operation() {
		getCollapsedFeatures();
		CollapseAllOperation collapseAll = new CollapseAllOperation(featureModel, true);

		// execute directly and push not in operation history otherwise no more than one undo possible
		collapseAll.operation();
		for (IFeature feature : iConstraint.getContainedFeatures()) {
			expandParents(feature);
		}
		return new FeatureIDEEvent(featureModel.getStructure().getRoot().getFeature(), EventType.COLLAPSED_CHANGED);
	}
	
	@Override
	protected FeatureIDEEvent inverseOperation() {
		CollapseAllOperation collapseAll = new CollapseAllOperation(featureModel, true);

		// execute directly and push not in operation history otherwise no more than one undo possible
		collapseAll.operation();
		for (IFeature f : affectedFeatureList) {
			expandFeature(f.getStructure());
		}
		return new FeatureIDEEvent(featureModel.getStructure().getRoot().getFeature(), EventType.COLLAPSED_CHANGED);
	}
	
	/**
	 * Collects all features that are not collapsed from the featureModel.
	 */
	private void getCollapsedFeatures() {
		for (IFeature f : featureModel.getFeatures()) {
			if (!f.getStructure().isCollapsed()) {
				affectedFeatureList.add(f);
			}
		}
	}
	
	/**
	 * Expands a single feature.
	 * @param featureStructure
	 */
	private void expandFeature(IFeatureStructure featureStructure) {
		featureStructure.setCollapsed(false);
		featureModel.fireEvent(new FeatureIDEEvent(featureStructure.getFeature(), EventType.COLLAPSED_CHANGED));
	}
}
