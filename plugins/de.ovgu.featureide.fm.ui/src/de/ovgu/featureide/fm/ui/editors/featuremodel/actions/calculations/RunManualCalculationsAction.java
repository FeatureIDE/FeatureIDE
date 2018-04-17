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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions.calculations;

import static de.ovgu.featureide.fm.core.localization.StringTable.RUN_MANUAL_CALCULATIONS;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Action to specify feature model analysis.<br> A manual call of the feature model analysis.
 *
 * @author Jens Meinicke
 * @author Marcus Pinnecke
 */
public class RunManualCalculationsAction extends Action {

	public static final String ID = "de.ovgu.featureide.runmanualcalculations";

	private final IFeatureModel featureModel;

	public RunManualCalculationsAction(GraphicalViewerImpl viewer, IFeatureModel featureModel) {
		super(RUN_MANUAL_CALCULATIONS);
		setImageDescriptor(FMUIPlugin.getDefault().getImageDescriptor("icons/thread_obj.gif"));
		this.featureModel = featureModel;
		setId(ID);
	}

	@Override
	public void run() {
		final boolean oldValue = featureModel.getAnalyser().runCalculationAutomatically;
		featureModel.getAnalyser().runCalculationAutomatically = true;
		featureModel.fireEvent(new FeatureIDEEvent(featureModel, EventType.REDRAW_DIAGRAM));
		featureModel.getAnalyser().runCalculationAutomatically = oldValue;
	}

}
