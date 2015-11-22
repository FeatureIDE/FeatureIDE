/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONSTRAINT;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FeatureModelFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * Operation with functionality to create a new constraint. Enables undo/redo
 * functionality.
 * 
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class ConstraintCreateOperation extends AbstractFeatureModelOperation {
	private final static String LABEL = CREATE_CONSTRAINT;
	private IConstraint constraint;

	/**
	 * @param node
	 *            the node representing the constraint to be added
	 * @param featureModel
	 *            model that will be used to add the constraint
	 */
	public ConstraintCreateOperation(Node node, IFeatureModel featureModel) {
		super(featureModel, LABEL);
		constraint = FeatureModelFactory.getInstance().createConstraint(featureModel, node);
	}

	@Override
	protected void redo() {
		featureModel.addConstraint(constraint);

		//initialize constraint position in manual layout
		if (!featureModel.getGraphicRepresenation().getLayout().hasFeaturesAutoLayout())
			FeatureDiagramLayoutHelper.initializeConstraintPosition(featureModel, featureModel.getConstraintCount() - 1);
	}

	@Override
	protected void undo() {
		featureModel.removeConstraint(constraint);
	}

}
