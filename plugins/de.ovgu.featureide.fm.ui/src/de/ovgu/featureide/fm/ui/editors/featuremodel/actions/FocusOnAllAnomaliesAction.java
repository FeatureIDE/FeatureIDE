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

import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.FeatureDiagramViewer;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FocusOnAnomaliesOperation;

/**
 * {@link FocusOnAllAnomaliesAction} extends {@link FocusOnAnomaliesAction} to focus on all features involved in some anomaly.
 *
 * @author Benedikt Jutz
 */
public class FocusOnAllAnomaliesAction extends FocusOnAnomaliesAction {

	public static final String ID = "de.ovgu.featureide.collapseallbotanomalous";

	public FocusOnAllAnomaliesAction(FeatureDiagramViewer viewer) {
		super(viewer, StringTable.FOCUS_ON_ALL_ANOMALIES);
	}

	/*
	 * (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.editors.featuremodel.actions.FocusOnAnomaliesAction#getAnomalyFocusOperation()
	 */
	@Override
	protected FocusOnAnomaliesOperation getAnomalyFocusOperation() {
		return FocusOnAnomaliesOperation.createAllAnomaliesFocusOperation(fm);
	}

}
