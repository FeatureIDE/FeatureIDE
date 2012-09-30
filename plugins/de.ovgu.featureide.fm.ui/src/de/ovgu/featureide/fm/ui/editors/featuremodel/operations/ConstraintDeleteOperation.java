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

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * TODO @Fabian description
 * 
 * @author Fabian Benduhn
 */
public class ConstraintDeleteOperation extends AbstractFeatureModelOperation {

	private static final String LABEL = "Delete Constraint";
	private Constraint constraint;
	
	private int index;

	public ConstraintDeleteOperation(Constraint constraint,
			FeatureModel featureModel) {
		super(featureModel, LABEL);
		this.constraint = constraint;
	}

	@Override
	protected void redo() {
		index = featureModel.getConstraintIndex(constraint);
		featureModel.removePropositionalNode(constraint);
	}

	@Override
	protected void undo() {
		featureModel.addConstraint(constraint, index);
		//initialize constraint position in manual layout
		if(!featureModel.getLayout().hasFeaturesAutoLayout())
			FeatureDiagramLayoutHelper.initializeConstraintPosition(featureModel,
				featureModel.getConstraintCount()-1);
	}

}
