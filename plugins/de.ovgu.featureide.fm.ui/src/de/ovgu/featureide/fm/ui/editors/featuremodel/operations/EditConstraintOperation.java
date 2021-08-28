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
 */
public class EditConstraintOperation extends AbstractFeatureModelOperation {

	private final int constraintIndex;

	/**
	 * This wrapper is used to wrap both fields (node and description) of a constraint It is needed because the FeatureIDEEvent constructor expects only one set
	 * of objects (oldState and newState) This way it is possible to cache the state of two different fields.
	 */
	public static class ConstraintDescription {

		private final Node node;
		private final String description;

		public ConstraintDescription(Node node, String description) {
			this.node = node;
			this.description = description;
		}

		public Node getNode() {
			return node;
		}

		public String getDescription() {
			return description;
		}
	}

	private final ConstraintDescription newWrapper;
	private final ConstraintDescription oldWrapper;

	public EditConstraintOperation(IFeatureModelManager featureModelManager, IConstraint constraint, Node propNode, String description) {
		super(featureModelManager, EDIT_CONSTRAINT);
		oldWrapper = new ConstraintDescription(constraint.getNode(), constraint.getDescription());
		newWrapper = new ConstraintDescription(propNode, description);
		constraintIndex = featureModelManager.getSnapshot().getConstraintIndex(constraint);
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(constraintIndex);
		constraint.setNode(newWrapper.getNode());
		constraint.setDescription(newWrapper.getDescription());
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, oldWrapper, newWrapper);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IConstraint constraint = featureModel.getConstraints().get(constraintIndex);
		constraint.setNode(oldWrapper.getNode());
		constraint.setDescription(oldWrapper.getDescription());
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, newWrapper, oldWrapper);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
