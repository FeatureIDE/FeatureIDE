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

import java.util.List;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.attributes.base.IFeatureAttribute;
import de.ovgu.featureide.fm.attributes.view.FeatureAttributeView;
import de.ovgu.featureide.fm.attributes.view.operations.RemoveFeatureAttributeOperation;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Action for the {@link FeatureAttributeView}. Is used to to remove the currently selected feature attribute.
 * 
 * @author Joshua Sprey
 * @author Chico Sundermann
 */
public class RemoveFeatureAttributeAction extends Action {

	private final IFeatureModelManager fmManager;
	private final List<IFeatureAttribute> attributes;

	public RemoveFeatureAttributeAction(IFeatureModelManager fmManager, List<IFeatureAttribute> attributes) {
		super(StringTable.REMOVE_SELECTED_ATTRIBUTE);
		this.fmManager = fmManager;
		this.attributes = attributes;
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new RemoveFeatureAttributeOperation(fmManager, attributes));
	}

	@Override
	public boolean isEnabled() {
		return attributes.size() > 0;
	}

}
