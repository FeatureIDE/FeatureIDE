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
package de.ovgu.featureide.ui.actions;

import org.eclipse.jface.action.Action;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.ProfileManager;
import de.ovgu.featureide.fm.core.ProfileManager.Project.Profile;
import de.ovgu.featureide.fm.ui.PlugInProfileSerializer;

/**
 * This class enables you to switch profiles
 * 
 * @author Jonas Weigt
 * @author Christian Harnisch
 */

public class SetProfileColorSchemeAction extends Action {
	private FeatureModel model;
	private String newProfileColorSchemeName;

	/*
	 * Constructor
	 */
	public SetProfileColorSchemeAction(String text, int style, FeatureModel model) {
		super(text, Action.AS_CHECK_BOX);
		this.model = model;
		this.newProfileColorSchemeName = text;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.collaboration.color.action.AbstractColorAction#action(de.ovgu.featureide.fm.core.Feature)
	 * 
	 * this method changes selected Colorscheme and saves the configuration 
	 */
	public void run() {
		ProfileManager.Project projet = ProfileManager.getProject(model.xxxGetEclipseProjectPath(), PlugInProfileSerializer.FEATURE_PROJECT_SERIALIZER);
		Profile p = projet.getProfile(newProfileColorSchemeName);
		if (!projet.getActiveProfile().getName().equals(p.getName())) {
			p.setAsActiveProfile();

		}
		
		

	}
}
