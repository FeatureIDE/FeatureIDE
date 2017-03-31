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
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.fm.core.localization.StringTable;

/**
 * A simple wizard for selecting a color scheme and applying it.
 * If necessary, new color schemes can be created.
 * 
 * @author Niklas Lehnfeld
 * @author Paul Maximilian Bittner
 */
public class SelectColorSchemeWizard extends Wizard {

	private SelectColorSchemePage page;
	private IFeatureModel featureModel;
	
	public SelectColorSchemeWizard(IFeatureModel featureModel) {
		super();
		setWindowTitle(StringTable.SELECT_COLOR_SCHEME);
		this.featureModel = featureModel;
	}

	public void addPages() {
		page = new SelectColorSchemePage(featureModel);
		addPage(page);
	}

	@Override
	public boolean performFinish() {
		final String csName = page.getColorSchemeName();
		if (csName != null && !csName.isEmpty() && FeatureColorManager.hasColorScheme(featureModel, csName)) {
			FeatureColorManager.setActive(featureModel, csName);
			return true;
		}
		
		return false;
	}
}
