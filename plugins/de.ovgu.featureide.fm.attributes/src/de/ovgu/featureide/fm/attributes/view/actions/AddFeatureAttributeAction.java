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
package de.ovgu.featureide.fm.attributes.view.actions;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.attributes.view.operations.AddFeatureAttributeOperation;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Action used to create an attribute. Depending on the {@link #attributeType} the action creates an attribute of the given type.
 *
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class AddFeatureAttributeAction extends Action {

	private final FeatureModelManager fmManager;
	private final String featureName;
	private final String attributeType;

	public AddFeatureAttributeAction(FeatureModelManager fmManager, String featureName, String attributeType, String actionName) {
		super(actionName);
		this.fmManager = fmManager;
		this.featureName = featureName;
		this.attributeType = attributeType;
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new AddFeatureAttributeOperation(fmManager, featureName, attributeType, getText()));
	}
}
