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

import static de.ovgu.featureide.fm.core.localization.StringTable.RENAME_FEATURE;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;

/**
 * Operation with functionality to rename features. Provides undo/redo functionality.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class RenameFeatureOperation extends AbstractFeatureModelOperation {

	private final String oldName;
	private final String newName;

	public RenameFeatureOperation(IFeatureModel featureModel, String oldName, String newName) {
		super(featureModel, RENAME_FEATURE);
		this.oldName = oldName;
		this.newName = newName;
	}

	@Override
	protected FeatureIDEEvent operation() {
		featureModel.getRenamingsManager().renameFeature(oldName, newName);
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_NAME_CHANGED, oldName, newName);
	}

	@Override
	protected FeatureIDEEvent inverseOperation() {
		featureModel.getRenamingsManager().renameFeature(newName, oldName);
		return new FeatureIDEEvent(featureModel, EventType.FEATURE_NAME_CHANGED, newName, oldName);
	}

}
