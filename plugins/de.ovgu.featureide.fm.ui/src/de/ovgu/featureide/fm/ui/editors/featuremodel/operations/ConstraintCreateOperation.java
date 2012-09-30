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

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * Operation with functionality to create a new constraint. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 */
public class ConstraintCreateOperation extends AbstractFeatureModelOperation {
	private final static String LABEL = "Create Constraint";
	private Constraint constraint;

	/**
	 * @param node
	 *            the node representing the constraint to be added
	 * @param featureModel
	 *            model that will be used to add the constraint
	 */
	public ConstraintCreateOperation(Node node, FeatureModel featureModel) {
		super(featureModel, LABEL);
		constraint = new Constraint(featureModel, node);
	}

	@Override
	protected void redo() {
		featureModel.addConstraint(constraint);
		
		//initialize constraint position in manual layout
		if(!featureModel.getLayout().hasFeaturesAutoLayout())
			FeatureDiagramLayoutHelper.initializeConstraintPosition(featureModel,
				 featureModel.getConstraintCount()-1);
	}

	@Override
	protected void undo() {
		featureModel.removePropositionalNode(constraint);
	}

}