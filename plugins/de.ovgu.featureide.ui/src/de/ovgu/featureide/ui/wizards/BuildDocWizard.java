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
package de.ovgu.featureide.ui.wizards;

import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.ChooseFeaturePage;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Wizard for the {@link BuildExtendedModulesHandler}.
 *
 * @author Reimar Schroeter
 */
public class BuildDocWizard extends AbstractWizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.BuildExtendedModulesWizard";

	private final String defaultFolderString;
	private final boolean featureSelection;

	public BuildDocWizard(String title, String defaultFolderString, boolean featureSelection) {
		super(title);
		this.defaultFolderString = (defaultFolderString != null) ? defaultFolderString : "";
		this.featureSelection = featureSelection;
	}

	@Override
	public void addPages() {
		if (featureSelection) {
			addPage(new ChooseFeaturePage());
		}
//		addPage(new ChooseFolderPage(defaultFolderString));
		addPage(new DocArgumentsPage());
	}

	public String getDefaultFolderString() {
		return defaultFolderString;
	}
}
