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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import java.util.Collections;
import java.util.List;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.IStructuredSelection;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;
import de.ovgu.featureide.fm.core.base.impl.MultiConstraint;
import de.ovgu.featureide.fm.core.base.impl.MultiFeature;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ConstraintEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.ModelElementEditPart;

/**
 * Abstract action for modifying a feature model.
 *
 * @author Sebastian Krieter
 */
public abstract class AFeatureModelAction extends Action {

	protected final IFeatureModelManager featureModelManager;

	public AFeatureModelAction(String title, String id, IFeatureModelManager featureModelManager) {
		super(title);
		setId(id);
		this.featureModelManager = featureModelManager;
		update();
	}

	public void update() {}

	@Override
	public boolean isEnabled() {
		// determine if the action has to be disabled to prevent editing imported features in other files
		if (!(this instanceof ActionAllowedInExternalSubmodel) && getInvolvedFeatures().stream().anyMatch(f -> isExternalFeature((IFeature) f))) {
			return false;
		}
		return super.isEnabled();
	}

	protected List<IFeature> getInvolvedFeatures() {
		return Collections.emptyList();
	}

	protected boolean isExternalFeature(IFeature feature) {
		return (feature != null) && (feature instanceof MultiFeature) && ((MultiFeature) feature).isFromExtern();
	}

	/**
	 * Tests if the selection in the editor includes an {@link IFeatureModelElement} from an external submodel.
	 *
	 * @param selection - {@link IStructuredSelection} The selection from the editor.
	 *
	 * @return boolean - true if selection is a {@link MultiFeature} or {@link MultiConstraint} from an external submodel, false otherwise.
	 */
	protected boolean hasExternalFeatureModelElement(IStructuredSelection selection) {
		for (final Object selectedElement : selection.toArray()) {
			if ((selectedElement instanceof FeatureEditPart) || (selectedElement instanceof ConstraintEditPart)) {
				final ModelElementEditPart editPart = (ModelElementEditPart) selectedElement;
				final IFeatureModelElement element = editPart.getModel().getObject();
				if (element instanceof IMultiFeatureModelElement) {
					final IMultiFeatureModelElement multiElement = (IMultiFeatureModelElement) element;
					if (multiElement.isFromExtern()) {
						return true;
					}
				}
			}
		}
		return false;
	}

}
