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

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

public abstract class MultiFeatureModelOperation extends AbstractFeatureModelOperation {

	protected final Deque<AbstractFeatureModelOperation> operations = new LinkedList<>();

	public MultiFeatureModelOperation(IFeatureModel featureModel, String name) {
		super(featureModel, name);
	}

	@Override
	public IStatus execute(IProgressMonitor monitor, IAdaptable info) throws ExecutionException {
		createSingleOperations();
		return super.execute(monitor, info);
	}

	protected abstract void createSingleOperations();

	@Override
	protected FeatureIDEEvent operation() {
		for (final Iterator<AbstractFeatureModelOperation> it = operations.iterator(); it.hasNext();) {
			final AbstractFeatureModelOperation operation = it.next();
			if (operation.canRedo()) {
				operation.redo();
			}
		}
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		for (final Iterator<AbstractFeatureModelOperation> it = operations.descendingIterator(); it.hasNext();) {
			final AbstractFeatureModelOperation operation = it.next();
			if (operation.canUndo()) {
				operation.undo();
			}
		}
		return new FeatureIDEEvent(null, EventType.STRUCTURE_CHANGED);
	}

	public void addOperation(AbstractFeatureModelOperation operation) {
		operations.add(operation);
	}

}
