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
package de.ovgu.featureide.fm.ui.wizards;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * A wizard to show a sub feature model and its implicit dependencies. The sub feature model is read-only and not persistent.
 *
 * @author "Ananieva Sofia"
 */
public class SubtreeDependencyWizard extends AbstractWizard {

	/**
	 * The sub feature model which contains implicit constraints if there are any.
	 */
	private final IFeatureModel subFm;

	/**
	 * The origin feature model which contains the sub feature model.
	 */
	private final IFeatureModel completeFm;

	/**
	 * Constructor.
	 *
	 * @param title The title of the wizard page
	 * @param newModel The sub feature model
	 * @param completeModel The origin feature model
	 */
	public SubtreeDependencyWizard(String title, IFeatureModel newModel, IFeatureModel completeModel) {
		super(title);
		subFm = newModel;
		completeFm = completeModel;
	}

	/**
	 * Adds a page to a wizard.
	 */
	@Override
	public void addPages() {
		addPage(new SubtreeDependencyPage(subFm, completeFm));
	}

	/**
	 * Performs finishing actions when closing the wizard.
	 */
	@Override
	public boolean performFinish() {
		return true;
	}

}
