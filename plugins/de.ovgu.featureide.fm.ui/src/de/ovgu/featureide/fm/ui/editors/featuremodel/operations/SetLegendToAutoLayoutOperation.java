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

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Specifies whether the legend should be automatically layout.
 *
 * @author Joshua Sprey
 */
public class SetLegendToAutoLayoutOperation extends AbstractGraphicalFeatureModelOperation {

	public SetLegendToAutoLayoutOperation(IGraphicalFeatureModel featureModel) {
		super(featureModel, "");
	}

	@Override
	public FeatureIDEEvent operation(IFeatureModel featureModel) {
		graphicalFeatureModel.getLayout().setLegendAutoLayout(!graphicalFeatureModel.getLayout().hasLegendAutoLayout());
		return new FeatureIDEEvent(this, EventType.LEGEND_LAYOUT_CHANGED);
	}

	@Override
	public FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return operation(featureModel);
	}
}
