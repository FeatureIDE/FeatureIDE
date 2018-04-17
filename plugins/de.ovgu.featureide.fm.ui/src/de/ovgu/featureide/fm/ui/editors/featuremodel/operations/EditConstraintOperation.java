/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * Operation with functionality to edit a constraint. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Marlen Bernier
 * @author Dawid Szczepanski
 */
public class EditConstraintOperation extends AbstractFeatureModelOperation {

	private final IConstraint constraint;
	
	/**
	 * This wrapper is used to wrap both fields (node and description) of a constraint
	 * It is needed because the FeatureIDEEvent constructor expects only one set of objects 
	 * (oldState and newState)
	 * This way it is possible to cache the state of two different fields. 
	 */
	private class Wrapper {
		Node newNode;
		Node oldNode;
		String oldDescription;
		String newDescription;	
	}
	
	Wrapper newWrapper;
	Wrapper oldWrapper;

	public EditConstraintOperation(IFeatureModel featureModel, IConstraint constraint, Node propNode, String description) {
		super(featureModel, EDIT_CONSTRAINT);
		oldWrapper = new Wrapper();
		newWrapper = new Wrapper();
		this.constraint = constraint;
		newWrapper.newNode = propNode;
		oldWrapper.oldNode = constraint.getNode();
		newWrapper.newDescription = description;
		oldWrapper.oldDescription = constraint.getDescription();
	}

	@Override
	protected FeatureIDEEvent operation() {
		constraint.setNode(newWrapper.newNode);
		constraint.setDescription(newWrapper.newDescription);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, oldWrapper, newWrapper);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		constraint.setNode(oldWrapper.oldNode);
		constraint.setDescription(oldWrapper.oldDescription);
		return new FeatureIDEEvent(constraint, EventType.CONSTRAINT_MODIFY, newWrapper, oldWrapper);
	}

}
