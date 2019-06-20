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

import java.util.ArrayList;
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

public abstract class MultiFeatureModelOperation extends AbstractFeatureModelOperation {

	protected final Deque<AbstractFeatureModelOperation> operations = new LinkedList<>();

	protected final List<String> featureNames;
	private String commonAncestor;

	public MultiFeatureModelOperation(IFeatureModelManager featureModelManager, String name, List<String> featureNames) {
		super(featureModelManager, name);
		this.featureNames = featureNames;
	}

	protected abstract void createSingleOperations(IFeatureModel featureModel);

	protected abstract String getID();

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
		return new FeatureModelOperationEvent(getID(), EventType.STRUCTURE_CHANGED, events, null, getFeature(featureModel));
	}

	private IFeature getFeature(IFeatureModel featureModel) {
		return commonAncestor == null ? null : featureModel.getFeature(commonAncestor);
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final List<FeatureModelOperationEvent> events = new ArrayList<>(operations.size());
		for (final AbstractFeatureModelOperation operation : operations) {
			events.add((FeatureModelOperationEvent) operation.operation(featureModel));
		}
		return new FeatureModelOperationEvent(getID(), EventType.STRUCTURE_CHANGED, events, null, getFeature(featureModel));
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final List<FeatureModelOperationEvent> events = new ArrayList<>(operations.size());
		for (final AbstractFeatureModelOperation operation : operations) {
			events.add((FeatureModelOperationEvent) operation.inverseOperation(featureModel));
		}
		return new FeatureModelOperationEvent(getID(), EventType.STRUCTURE_CHANGED, events, null, getFeature(featureModel));
	}

	public void addOperation(AbstractFeatureModelOperation operation) {
		operations.add(operation);
	}

}
