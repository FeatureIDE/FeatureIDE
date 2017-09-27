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

import org.eclipse.jface.wizard.Wizard;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * Wizard for managing color schemes for a given feature model. Can select, rename, delete, and create color schemes.
 *
 * @author Sebastian Krieter
 */
public class ColorSchemeWizard extends Wizard {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".wizards.ManageColorSchemesWizard";

	private final IFeatureModel featureModel;

	public ColorSchemeWizard(IFeatureModel featureModel) {
		super();
		setWindowTitle("Color-Scheme Manager");
		this.featureModel = featureModel;
	}

	@Override
	public void addPages() {
		addPage(new ColorSchemePage(featureModel));
	}

	@Override
	public boolean performFinish() {
		return true;
	}

}
