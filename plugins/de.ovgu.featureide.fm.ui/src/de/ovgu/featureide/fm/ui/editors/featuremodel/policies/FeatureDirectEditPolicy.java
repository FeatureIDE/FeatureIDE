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
package de.ovgu.featureide.fm.ui.editors.featuremodel.policies;

import org.eclipse.gef.commands.Command;
import org.eclipse.gef.editpolicies.DirectEditPolicy;
import org.eclipse.gef.requests.DirectEditRequest;

import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.commands.FeatureRenamingCommand;

/**
 * Allows to rename features at the feature diagram.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureDirectEditPolicy extends DirectEditPolicy {

	private final IGraphicalFeatureModel featureModel;

	private final IGraphicalFeature feature;

	public FeatureDirectEditPolicy(IGraphicalFeatureModel featureModel, IGraphicalFeature feature) {
		this.featureModel = featureModel;
		this.feature = feature;
	}

	@Override
	protected Command getDirectEditCommand(DirectEditRequest request) {
		final String newName = (String) request.getCellEditor().getValue();
		return new FeatureRenamingCommand(featureModel.getFeatureModel(), feature.getObject().getName(), newName);
	}

	@Override
	protected void showCurrentEditValue(DirectEditRequest request) {}

}
