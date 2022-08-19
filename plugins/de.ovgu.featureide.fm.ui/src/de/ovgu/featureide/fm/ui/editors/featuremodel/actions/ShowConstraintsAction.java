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

import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_CONSTRAINTS;

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.ShowConstraintsOperation;

/**
 * Action to show/hide constraints beneath the feature model
 *
 * @author Rahel Arens
 */
public class ShowConstraintsAction extends Action {

	public static final String ID = "de.ovgu.featureide.hideconstraints";

	private final IGraphicalFeatureModel featureModel;

	public ShowConstraintsAction(GraphicalViewerImpl viewer, IGraphicalFeatureModel featureModel) {
		super(SHOW_CONSTRAINTS);
		this.featureModel = featureModel;
		setId(ID);
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new ShowConstraintsOperation(featureModel));
	}

}
