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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnAnomaliesOperation;

/**
 * The {@link FocusOnAnomaliesAction} collapses all features but those affected by a given feature model anomaly type.
 *
 * @author Benedikt Jutz
 */
public abstract class FocusOnAnomaliesAction extends Action {

	/**
	 * <code>fm</code> stores the graphical feature model whose features we expand or collapse.
	 */
	protected final IGraphicalFeatureModel fm;

	/**
	 * Creates a new {@link FocusOnAnomaliesAction}
	 *
	 * @param fm - {@link IGraphicalFeatureModel}
	 * @param name - {@link String}
	 */
	protected FocusOnAnomaliesAction(IGraphicalFeatureModel fm, String name) {
		super(name);
		this.fm = fm;
	}

	/**
	 * Executes the appropriate {@link FocusOnAnomaliesOperation}.
	 *
	 * @see {@link Action#run}
	 */
	@Override
	public void run() {
		FeatureModelOperationWrapper.run(getAnomalyFocusOperation());
		fm.getFeatureModelManager().getVarObject().fireEvent(FeatureIDEEvent.getDefault(EventType.REDRAW_DIAGRAM));
	}

	/**
	 * Returns the appropriate {@link FocusOnAnomaliesAction} that specifies on which anomalies we focus on.
	 *
	 * @return new {@link FocusOnAnomaliesOperation}
	 */
	protected abstract FocusOnAnomaliesOperation getAnomalyFocusOperation();
}
