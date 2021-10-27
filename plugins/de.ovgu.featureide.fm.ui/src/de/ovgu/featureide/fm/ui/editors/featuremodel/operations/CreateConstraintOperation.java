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

import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_CONSTRAINT;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to create a new constraint. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class CreateConstraintOperation extends ExternalFeatureModelOperation {

	/**
	 * <code>node</code> holds the boolean formula of the constraint.
	 */
	private final Node node;
	/**
	 * <code>description</code> holds the constraints description.
	 */
	private final String description;
	/**
	 * <code>constraintID</code> saves the index the constraint was given.
	 */
	private long constraintID = -1;
	/**
	 * <code>createdConstraint</code> stores the created constraint for REDO operations.
	 */
	private IConstraint createdConstraint;

	/**
	 * The standard {@link CreateConstraintOperation} constructor.
	 *
	 * @param node - {@link Node} representing the constraint to be added.
	 * @param featureModelManager - {@link IFeatureModelManager} The manager for the model to add the constraint to.
	 * @param description - {@link String} Textual description.
	 */
	public CreateConstraintOperation(Node node, IFeatureModelManager featureModelManager, String description) {
		super(featureModelManager, CREATE_CONSTRAINT);
		this.node = node;
		this.description = description;
	}

	public CreateConstraintOperation(Node node, IFeatureModelManager featureModelManager, String description, int type) {
		super(featureModelManager, CREATE_CONSTRAINT, type);
		this.node = node;
		this.description = description;
	}

	/**
	 * Adds a new constraint to <code>featureModel</code> and stores its ID. Assigns a description and external model type, if required, and stores its ID for
	 * deletion. <br> For a redo, this method clones <code>createdConstraint</code> instead.
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final int constraintCount = featureModel.getConstraintCount();
		final IFeatureModelFactory featureModelFactory = FMFactoryManager.getInstance().getFactory(featureModel);
		final IConstraint constraint;

		if (createdConstraint == null) {
			createdConstraint = featureModelFactory.createConstraint(featureModel, node);
			constraint = createdConstraint;
			constraintID = constraint.getInternalId();
			constraint.setDescription(description);
			setType(constraint);
		} else {
			constraint = featureModelFactory.copyConstraint(featureModel, createdConstraint);
		}
		featureModel.addConstraint(constraint, constraintCount);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_ADD, null, constraint);
	}

	/**
	 * Deletes the constraint identified by <code>constraintID</code>.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = (IConstraint) featureModel.getElement(constraintID);
		featureModel.removeConstraint(constraint);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_DELETE, constraint, null);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
