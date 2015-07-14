/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_COLORSCHEME;

import org.eclipse.jface.wizard.Wizard;

import de.ovgu.featureide.fm.core.ColorschemeTable;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * A wizard for adding a new color scheme.
 * 
 * @author Sebastian Krieter
 */
public class NewColorSchemeWizard extends Wizard {

	public static final String ID = UIPlugin.PLUGIN_ID
			+ ".wizards.NewColorSchemeWizard";

	public NewColorSchemePage page;
	
	private FeatureModel featureModel;

	public NewColorSchemeWizard(FeatureModel featureModel) {
		super();
		setWindowTitle(NEW_COLORSCHEME);
		this.featureModel = featureModel;
	}

	public void addPages() {
		page = new NewColorSchemePage();
		addPage(page);
	}

	public boolean performFinish() {
		final String csName = page.getColorSchemeName();
		if (csName != null && !csName.isEmpty()) {
			ColorschemeTable colorschemeTable = featureModel.getColorschemeTable();
			colorschemeTable.addColorscheme(csName);
			if (page.isCurColorScheme()) {
				colorschemeTable.setSelectedColorscheme(colorschemeTable.size());
			}
			return true;
		} else {
			return false;
		}
	}
}
