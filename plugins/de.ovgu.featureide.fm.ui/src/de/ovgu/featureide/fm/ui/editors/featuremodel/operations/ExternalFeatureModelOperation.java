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

import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.base.IMultiFeatureModelElement;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

/**
 * {@link ExternalFeatureModelOperation} is an abstract subclass for operations that add new features or constraints in {@link MultiFeatureModel}s. These
 * operations need to set the new {@link IMultiFeatureModelElement}'s type correctly, depending on how they are imported.
 *
 * @author Benedikt Jutz
 */
public abstract class ExternalFeatureModelOperation extends AbstractFeatureModelOperation {

	/**
	 * <code>type</code> stores the type of the newly added element.
	 */
	protected final int type;

	/**
	 * Reusable default constructor for when the type is irrelevant.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param title - {@link String}
	 */
	public ExternalFeatureModelOperation(IFeatureModelManager featureModelManager, String title) {
		this(featureModelManager, title, IMultiFeatureModelElement.TYPE_INTERN);
	}

	/**
	 * Creates a new {@link ExternalFeatureModelOperation}.
	 *
	 * @param featureModelManager - {@link IFeatureModelManager}
	 * @param title - {@link String}
	 * @param type - int
	 */
	public ExternalFeatureModelOperation(IFeatureModelManager featureModelManager, String title, int type) {
		super(featureModelManager, title);
		this.type = type;
	}

	/**
	 * Assigns the correct type to <code>element</code>. Does nothing for normal {@link IFeatureModelElement}s.
	 *
	 * @param element - {@link IFeatureModelElement}
	 */
	protected void setType(IFeatureModelElement element) {
		if (element instanceof IMultiFeatureModelElement) {
			((IMultiFeatureModelElement) element).setType(type);
		}
	}
}
