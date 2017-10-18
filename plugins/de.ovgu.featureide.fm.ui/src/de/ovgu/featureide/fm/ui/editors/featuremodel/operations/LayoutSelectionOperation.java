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

import static de.ovgu.featureide.fm.core.localization.StringTable.SET;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutHelper;

/**
 * Operation to select the layout for the feature model editor.
 *
 * @author Marcus Pinnecke (Feature interface)
 */
public class LayoutSelectionOperation extends AbstractGraphicalFeatureModelOperation {

	private final int newSelectedLayoutAlgorithm;
	private final int oldSelectedLayoutAlgorithm;

	public LayoutSelectionOperation(IGraphicalFeatureModel featureModel, int newSelectedLayoutAlgorithm, int oldSelectedLayoutAlgorithm) {
		super(featureModel, SET + FeatureDiagramLayoutHelper.getLayoutLabel(newSelectedLayoutAlgorithm));
		this.newSelectedLayoutAlgorithm = newSelectedLayoutAlgorithm;
		this.oldSelectedLayoutAlgorithm = oldSelectedLayoutAlgorithm;
	}

	@Override
	protected FeatureIDEEvent operation() {
		graphicalFeatureModel.getLayout().setLayout(newSelectedLayoutAlgorithm);
		return new FeatureIDEEvent(null, EventType.MODEL_LAYOUT_CHANGED);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		graphicalFeatureModel.getLayout().setLayout(oldSelectedLayoutAlgorithm);
		return new FeatureIDEEvent(null, EventType.MODEL_LAYOUT_CHANGED);
	}

}
