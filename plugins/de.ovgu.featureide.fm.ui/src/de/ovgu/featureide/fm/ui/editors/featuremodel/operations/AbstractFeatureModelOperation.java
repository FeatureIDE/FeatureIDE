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

import javax.annotation.Nonnull;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent.ExecutionType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * This operation should be used as superclass for all operations on the feature model. It provides standard handling and refreshing of the model.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public abstract class AbstractFeatureModelOperation {

	protected static final String ID_PREFIX = PluginID.PLUGIN_ID + ".operation.";

	protected final IFeatureModelManager featureModelManager;
	protected final String title;

	public AbstractFeatureModelOperation(IFeatureModelManager featureModelManager, String title) {
		this.featureModelManager = featureModelManager;
		this.title = title;
	}

	protected abstract FeatureIDEEvent operation(IFeatureModel featureModel);

	protected abstract FeatureIDEEvent inverseOperation(IFeatureModel featureModel);

	protected FeatureIDEEvent firstOperation(IFeatureModel featureModel) {
		return operation(featureModel);
	}

	public final void execute() {
		final FeatureIDEEvent event = featureModelManager.processObject(this::firstOperation, getChangeIndicator());
		if (event instanceof FeatureModelOperationEvent) {
			((FeatureModelOperationEvent) event).setExecutionType(ExecutionType.EXECUTE);
		}
		fireEvent(event);
	}

	public final void redo() {
		final FeatureIDEEvent event = featureModelManager.processObject(this::operation, getChangeIndicator());
		if (event instanceof FeatureModelOperationEvent) {
			((FeatureModelOperationEvent) event).setExecutionType(ExecutionType.REDO);
		}
		fireEvent(event);
	}

	public final void undo() {
		final FeatureIDEEvent event = featureModelManager.processObject(this::inverseOperation, getChangeIndicator());
		if (event instanceof FeatureModelOperationEvent) {
			((FeatureModelOperationEvent) event).setExecutionType(ExecutionType.UNDO);
		}
		fireEvent(event);
	}

	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ALL;
	}

	protected final void fireEvent(@Nonnull FeatureIDEEvent event) {
		if (event == null) {
			Logger.logWarning(getClass() + " operation() must return a FeatureIDEEvent");
			event = new FeatureIDEEvent(featureModelManager, null, null, null);
		}
		featureModelManager.fireEvent(event);
	}

	IFeatureModelManager getFeatureModelManager() {
		return featureModelManager;
	}

	public String getTitle() {
		return title;
	}

}
