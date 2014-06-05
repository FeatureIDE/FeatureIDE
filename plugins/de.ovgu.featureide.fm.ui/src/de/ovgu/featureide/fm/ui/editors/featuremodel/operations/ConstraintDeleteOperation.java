/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import de.ovgu.featureide.fm.core.Constraint;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * Operation to delete a constraint.
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
		featureModel.removeConstraint(constraint);
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
