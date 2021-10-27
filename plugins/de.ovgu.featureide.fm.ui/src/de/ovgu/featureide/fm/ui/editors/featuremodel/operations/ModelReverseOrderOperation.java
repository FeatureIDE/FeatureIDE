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

import static de.ovgu.featureide.fm.core.localization.StringTable.REVERSE_LAYOUT_ORDER;

import java.util.ArrayList;
import java.util.Collections;

import de.ovgu.featureide.fm.core.Features;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.FeatureUIHelper;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation with functionality to reverse the feature model layout order from a given root. Enables undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 * @author Benedikt Jutz
 */
public class ModelReverseOrderOperation extends AbstractFeatureModelOperation {

	/**
	 * The string label for this operation.
	 */
	private static final String LABEL = REVERSE_LAYOUT_ORDER;
	/**
	 * The root feature from which to reverse.
	 */
	private final IFeature rootFeature;

	/**
	 * Creates a new {@link ModelReverseOrderOperation} for the given root of <code>featureModel</code>.
	 *
	 * @param featureModel - {@link IGraphicalFeatureModel}
	 */
	public ModelReverseOrderOperation(IGraphicalFeatureModel featureModel) {
		super(featureModel.getFeatureModelManager(), LABEL);
		rootFeature = FeatureUIHelper.getGraphicalRootFeature(featureModel).getObject();
	}

	/**
	 * Creates a new {@link ModelReverseOrderOperation} for <code>rootFeature</code>.
	 *
	 * @param rootFeature - {@link IFeature}
	 */
	public ModelReverseOrderOperation(IFeature rootFeature) {
		super(FeatureModelManager.getInstance(rootFeature.getFeatureModel()), LABEL);
		this.rootFeature = rootFeature;
	}

	/**
	 * Reverses the children of all compound features that are reachable from <code>rootStructure</code>, and then returns a {@link FeatureIDEEvent} with the
	 * <code>LOCATION_CHANGED</code>, <code>featureModel</code> as source, and <code>rootStructure</code> as new value.
	 *
	 * @see {@link AbstractFeatureModelOperation#operation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeatureStructure rootStructure = rootFeature.getStructure();
		for (final IFeatureStructure feature : Features.getCompoundFeatures(new ArrayList<IFeatureStructure>(), rootStructure)) {
			Collections.reverse(feature.getChildren());
		}
		return new FeatureIDEEvent(featureModel, EventType.LOCATION_CHANGED, null, rootFeature);
	}

	/**
	 * Executes the operation again, thus reversing it.
	 *
	 * @see {@link AbstractFeatureModelOperation#inverseOperation(IFeatureModel)}
	 */
	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		return operation(featureModel);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_ORDER;
	}

}
