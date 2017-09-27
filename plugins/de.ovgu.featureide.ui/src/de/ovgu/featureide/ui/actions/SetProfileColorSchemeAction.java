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
package de.ovgu.featureide.ui.actions;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.color.DefaultColorScheme;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;

/**
 * This class enables you to switch profiles
 *
 * @author Jonas Weigt
 * @author Christian Harnisch
 * @author Marcus Pinnecke
 */

public class SetProfileColorSchemeAction extends Action {

	private final IFeatureModel model;
	private final String newProfileColorSchemeName;

	/*
	 * Constructor
	 */
	public SetProfileColorSchemeAction(String text, int style, IFeatureModel model) {
		super(text, style);
		this.model = model;
		newProfileColorSchemeName = text;
	}

	/**
	 * Changes selected color scheme and saves the configuration
	 */
	@Override
	public void run() {
		String clrSchemeName = newProfileColorSchemeName;

		if (FeatureColorManager.isCurrentColorScheme(model, clrSchemeName)) {
			clrSchemeName = DefaultColorScheme.defaultName;
		}

		FeatureColorManager.setActive(model, clrSchemeName);
	}
}
