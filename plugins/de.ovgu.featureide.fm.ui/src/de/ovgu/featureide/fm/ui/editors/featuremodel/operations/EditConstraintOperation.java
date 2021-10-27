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

import static de.ovgu.featureide.fm.core.localization.StringTable.EDIT_CONSTRAINT;

import java.util.Set;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Operation with functionality to edit a constraint. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 * @author Benedikt Jutz
 */
public class EditConstraintOperation extends AbstractFeatureModelOperation {

	/**
	 * This wrapper holds the constraint fields (node, description and tags) of a constraint. In this way, we can store the fields for the old and new
	 * constraints in only two objects (oldValue and newValue) like the {@link FeatureIDEEvent} constructor expects.
	 */
	public static class ConstraintDescription {

		public final Node node;
		public final String description;
		public final Set<String> tags;

		public ConstraintDescription(Node node, String description, Set<String> tags) {
			this.node = node;
			this.description = description;
			this.tags = tags;
		}
	}

	/**
	 * <code>oldWrapper</code> holds the old Constraint.
	 */
	private final ConstraintDescription oldWrapper;
	/**
	 * <code>constraintIndex</code> contains the internal ID of <code>oldConstraint</code>.
	 */
	private final long constraintID;
	/**
	 * <code>newWrapper</code> holds the new constraint data we replace <code>oldWrapper</code> with.
	 */
	private final ConstraintDescription newWrapper;

	/**
	 * Creates a new {@link EditConstraintOperation}.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager} The manager for the feature model where we change the constraint.
	 * @param constraint - {@link IConstraint} The constraint to modify.
	 * @param propNode - {@link Node} The propositional formula that constraint now has.
	 * @param description - {@link String} The description <code>constraint</code> now has.
	 */
	public EditConstraintOperation(IFeatureModelManager featureModelManager, IConstraint constraint, Node propNode, String description, Set<String> tags) {
		super(featureModelManager, EDIT_CONSTRAINT);
		oldWrapper = new ConstraintDescription(constraint.getNode(), constraint.getDescription(), constraint.getTags());
		newWrapper = new ConstraintDescription(propNode, description, tags);
		constraintID = constraint.getInternalId();
	}

	/**
	 * Replaces the propositional formula and description of the constraint with the values in newWrapper. Returns a event of the
	 * {@link EventType#CONSTRAINT_MODIFY} type.
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IConstraint constraint = (IConstraint) featureModel.getElement(constraintID);
		constraint.setNode(newWrapper.node);
		constraint.setDescription(newWrapper.description);
		constraint.setTags(newWrapper.tags);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, oldWrapper, newWrapper);
	}

	/**
	 * The inverse operation for {@link EditConstraintOperation} replaces the now changed values with the previous ones stored in oldWrapper. Returns a event of
	 * the {@link EventType#CONSTRAINT_MODIFY} type.
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = (IConstraint) featureModel.getElement(constraintID);
		constraint.setNode(oldWrapper.node);
		constraint.setDescription(oldWrapper.description);
		constraint.setTags(oldWrapper.tags);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, newWrapper, oldWrapper);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
