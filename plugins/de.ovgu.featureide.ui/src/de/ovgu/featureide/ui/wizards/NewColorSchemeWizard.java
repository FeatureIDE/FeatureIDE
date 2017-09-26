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

import static de.ovgu.featureide.fm.core.localization.StringTable.NEW_COLORSCHEME;

import org.eclipse.jface.wizard.Wizard;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.CollaborationView;

/**
 * A wizard for adding a new color scheme.
 *
 * @author Sebastian Krieter
 */
public class NewColorSchemeWizard extends Wizard {

	public static final String ID = UIPlugin.PLUGIN_ID + ".wizards.NewColorSchemeWizard";

	public NewColorSchemePage page;

	private final IFeatureModel featureModel;

	public NewColorSchemeWizard(IFeatureModel featureModel, CollaborationView collaborationView) {
		super();
		setWindowTitle(NEW_COLORSCHEME);
		this.featureModel = featureModel;
	}

	@Override
	public void addPages() {
		page = new NewColorSchemePage();
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		final String csName = page.getColorSchemeName();
		if ((csName != null) && !csName.isEmpty() && !FeatureColorManager.hasColorScheme(featureModel, csName)) {
			FeatureColorManager.newColorScheme(featureModel, csName);
			if (page.isCurColorScheme()) {
				FeatureColorManager.setActive(featureModel, csName);
			}
			return true;
		} else {
			return false;
		}
	}
}
