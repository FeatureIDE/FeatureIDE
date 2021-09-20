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

import java.util.Map;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Collapses and/or expands features. Subclasses define which features get collapsed and/or expanded using {@link #createTargets()}. Subclasses should also
 * override {@link #operation()} and {@link #inverseOperation()} to return a specific event object.
 *
 * @author Timo G&uuml;nther
 */
public abstract class AbstractCollapseOperation extends AbstractGraphicalFeatureModelOperation {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param graphicalFeatureModel the graphical feature model
	 * @param label the label to display
	 */
	public AbstractCollapseOperation(IGraphicalFeatureModel graphicalFeatureModel, String label) {
		super(graphicalFeatureModel, label);
	}

	/**
	 * Creates the features to collapse or expand.
	 *
	 * @return the features to collapse or expand
	 * @see {@link #getTargets()}
	 */
	protected abstract Map<IGraphicalFeature, Boolean> createTargets();

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		createTargets().entrySet().forEach(entry -> entry.getKey().setCollapsed(entry.getValue()));
		return null;
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		createTargets().entrySet().forEach(entry -> entry.getKey().setCollapsed(!entry.getValue()));
		return null;
	}
}
