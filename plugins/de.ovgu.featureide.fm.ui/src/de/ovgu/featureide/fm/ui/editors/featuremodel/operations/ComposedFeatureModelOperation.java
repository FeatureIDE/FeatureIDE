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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * {@link ComposedFeatureModelOperation} extends {@link AbstractFeatureModelOperation} with the Composite pattern in order to run an operation that consists of
 * multiple other operations in the correct order.
 *
 * @author Sebastian Krieter
 * @author Jens Meinicke
 * @author Tobias Heß
 * @author Benedikt Jutz (Documentation)
 */
public abstract class ComposedFeatureModelOperation extends AbstractFeatureModelOperation {

	/**
	 * <code>operations</code> is a double-ended queue to store the single operations required to execute this {@link ComposedFeatureModelOperation}.
	 */
	protected final Deque<AbstractFeatureModelOperation> operations = new LinkedList<>();
	/**
	 * <code>featureNames</code> stores the feature names <code>operations</code> were executed on.
	 */
	protected final List<String> featureNames;
	/**
	 * <code>commonAncestor</code> contains the lowest common ancestor feature for the features in <code>featureNames</code>.
	 */
	private String commonAncestor;

	/**
	 * Creates a new {@link ComposedFeatureModelOperation}.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param name - {@link String}
	 * @param featureNames - {@link List}
	 */
	public ComposedFeatureModelOperation(IFeatureModelManager featureModelManager, String name, List<String> featureNames) {
		super(featureModelManager, name);
		this.featureNames = featureNames;
	}

	/**
	 * Constructs the single operations that need to be executed for this operation to run on <code>featureModel</code>.
	 *
	 * @param featureModel - {@link IFeatureModel}
	 */
	protected abstract void createSingleOperations(IFeatureModel featureModel);

	/**
	 * Returns the identifier of the concrete {@link ComposedFeatureModelOperation}. This identifier is also stored in the {@link FeatureModelOperationEvent}s that
	 * are fired.
	 *
	 * @return {@link String}
	 */
	protected abstract String getID();

	/**
	 * Runs this operation the first time. <br> In preparation, we call createSingleOperations to create the single operations to execute, then attempt to find
	 * the common ancestor of the features in <code>featureNames</code>. <br> Afterwards, we call
	 * {@link AbstractFeatureModelOperation#firstOperation(IFeatureModel)} for each operation in <code>operations</code>, and store the result in a
	 * {@link List}. The returned {@link FeatureModelOperationEvent} has the {@link EventType#MULTIPLE_CHANGES_OCCURRED} type, and stores the single events as
	 * new value.
	 *
	 * @see {@link AbstractFeatureModelOperation#firstOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent firstOperation(IFeatureModel featureModel) {
		createSingleOperations(featureModel);
		List<IFeature> commonAncestorList = null;
		for (final String name : featureNames) {
			final IFeature feature = featureModel.getFeature(name);
			if (feature != null) {
				commonAncestorList = Features.getCommonAncestor(commonAncestorList, FeatureUtils.getParent(feature));
			}
		}
		if ((commonAncestorList != null) && !commonAncestorList.isEmpty()) {
			commonAncestor = commonAncestorList.get(commonAncestorList.size() - 1).getName();
		}

		final List<FeatureModelOperationEvent> events = new ArrayList<>(operations.size());
		for (final AbstractFeatureModelOperation operation : operations) {
			events.add((FeatureModelOperationEvent) operation.firstOperation(featureModel));
		}
		return new FeatureModelOperationEvent(getID(), EventType.MULTIPLE_CHANGES_OCCURRED, featureModel, getFeature(featureModel), events);
	}

	/**
	 * Looks up and returns the feature named <code>commonAncestor</code> in the given <code>featureModel</code>. If <code>commonAncestor</code> is
	 * null/unknown, return null instead.
	 *
	 * @param featureModel - {@link IFeatureModel}t
	 * @return {@link IFeatureModel}
	 */
	private IFeature getFeature(IFeatureModel featureModel) {
		return commonAncestor == null ? null : featureModel.getFeature(commonAncestor);
	}

	/**
	 * Runs each operation in <code>operations</code> in-order, stores the resulting events in a list, and returns a {@link FeatureModelOperationEvent} again
	 * with the {@link EventType#MULTIPLE_CHANGES_OCCURRED} event type, and the events in-order.
	 *
	 * @see {@link AbstractFeatureModelOperation#operation(IFeatureModel)}
	 * @see {@link ComposedFeatureModelOperation#firstOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final List<FeatureModelOperationEvent> events = new ArrayList<>(operations.size());
		for (final AbstractFeatureModelOperation operation : operations) {
			events.add((FeatureModelOperationEvent) operation.operation(featureModel));
		}
		return new FeatureModelOperationEvent(getID(), EventType.MULTIPLE_CHANGES_OCCURRED, featureModel, getFeature(featureModel), events);
	}

	/**
	 * Runs the inverse operations for all operations in <code>operations</code> in reversed order. Otherwise works like
	 * {@link MultiFeatureModelOperation#operationIFeatureModel)}.
	 *
	 * @see {@link AbstractFeatureModelOperation#inverseOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final List<FeatureModelOperationEvent> events = new ArrayList<>(operations.size());
		final ArrayList<AbstractFeatureModelOperation> copiedList = new ArrayList<>(operations);
		Collections.reverse(copiedList);

		for (final AbstractFeatureModelOperation operation : operations) {
			events.add((FeatureModelOperationEvent) operation.inverseOperation(featureModel));
		}
		return new FeatureModelOperationEvent(getID(), EventType.MULTIPLE_CHANGES_OCCURRED, featureModel, getFeature(featureModel), events);
	}

	public void addOperation(AbstractFeatureModelOperation operation) {
		operations.add(operation);
	}

}