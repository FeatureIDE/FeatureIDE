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

import static de.ovgu.featureide.fm.core.localization.StringTable.ABSTRACT_OPERATION;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * Required to execute compound operations
 *
 * @author Chico Sundermann
 * @author Paul Westphal
 */
public class AbstractFeatureOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "AbstractFeatureOperation";

	private final String featureName;

	/**
	 * Whether the feature was implicit before the operation.
	 */
	private boolean implicitFeature = false;

	public AbstractFeatureOperation(String featureName, IFeatureModelManager featureModelManager) {
		super(featureModelManager, ABSTRACT_OPERATION);
		this.featureName = featureName;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		implicitFeature = feature.getProperty().isImplicit();
		feature.getProperty().setImplicit(false);
		return changeAbstract(feature);
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);
		feature.getProperty().setImplicit(implicitFeature);
		return changeAbstract(feature);
	}

	private FeatureIDEEvent changeAbstract(IFeature feature) {
		final boolean oldValue = feature.getStructure().isAbstract();
		final boolean newValue = !oldValue;
		feature.getStructure().setAbstract(newValue);
		return new FeatureModelOperationEvent(ID, EventType.ATTRIBUTE_CHANGED, feature, oldValue, newValue);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
