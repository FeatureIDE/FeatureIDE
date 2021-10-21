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

import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE_CONSTRAINT;

import java.util.Optional;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent.EventType;
import de.ovgu.featureide.fm.core.base.event.FeatureModelOperationEvent;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * Operation to delete a constraint.
 *
 * @author Fabian Benduhn
 * @author Marcus Pinnecke
 */
public class DeleteConstraintOperation extends AbstractFeatureModelOperation {

	public static final String ID = ID_PREFIX + "DeleteConstraintOperation";

	private final IConstraint oldConstraint;
	private int oldConstraintIndex;

	public DeleteConstraintOperation(IConstraint constraint, IFeatureModelManager featureModelManager) {
		super(featureModelManager, DELETE_CONSTRAINT);
		oldConstraint = constraint;
	}

	public IConstraint getOldConstraint() {
		return oldConstraint;
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		oldConstraintIndex = featureModel.getConstraintIndex(oldConstraint);
		if (oldConstraintIndex != -1) {
			featureModel.removeConstraint(oldConstraint);
		}
		return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_DELETE, featureModel, oldConstraint, null);
	}

	/**
	 * Disallows <code>inverseOperation</code>/adding <code>oldConstraint</code> back to the feature model if at least one feature in its formula doesn't appear
	 * in the feature model any more.
	 */
	@Override
	protected Optional<String> approveUndo() {
		final IFeatureModel model = featureModelManager.getVarObject();
		if (oldConstraint.getNode().getUniqueContainedFeatures().stream().anyMatch(name -> model.getFeature(name) == null)) {
			return Optional.of(StringTable.ONE_OR_MORE_FEATURES_OF_THIS_CONSTRAINT_HAVE_BEEN_DELETED);
		} else {
			return Optional.empty();
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		if (oldConstraintIndex != -1) {
			final IConstraint constraint = FMFactoryManager.getInstance().getFactory(featureModel).copyConstraint(featureModel, oldConstraint);
			featureModel.addConstraint(constraint, oldConstraintIndex);
			return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_ADD, featureModel, null, constraint);
		}
		return new FeatureModelOperationEvent(ID, EventType.CONSTRAINT_ADD, featureModel, null, null);
	}

	@Override
	protected int getChangeIndicator() {
		return FeatureModelManager.CHANGE_DEPENDENCIES;
	}

}
