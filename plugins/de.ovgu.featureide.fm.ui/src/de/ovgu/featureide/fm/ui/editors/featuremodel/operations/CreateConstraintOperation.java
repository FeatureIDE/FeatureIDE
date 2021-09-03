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
	 * <code>description</code> holds the constraint's description.
	 */
	private final String description;
	/**
	 * <code>constraintCount</code> saves the location the constraint was inserted at.
	 */
	private int constraintCount = -1;

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

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		constraintCount = featureModel.getConstraintCount();
		final IConstraint constraint = FMFactoryManager.getInstance().getFactory(featureModel).createConstraint(featureModel, node);
		constraint.setDescription(description);
		setType(constraint);
		featureModel.addConstraint(constraint, constraintCount);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_ADD, null, constraint);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(constraintCount);
		featureModel.removeConstraint(constraintCount);
		return new FeatureIDEEvent(featureModel, EventType.CONSTRAINT_DELETE, constraint, null);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
