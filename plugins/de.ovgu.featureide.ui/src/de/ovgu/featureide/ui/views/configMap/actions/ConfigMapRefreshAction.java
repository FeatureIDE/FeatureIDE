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
package de.ovgu.featureide.ui.views.configMap.actions;

import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.ImageDescriptor;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.configMap.ConfigurationMap;

/**
 * @author Niklas Lehnfeld
 * @author Mohammad Mahhouk
 */
public class ConfigMapRefreshAction extends Action {

	private final ConfigurationMap configMap;

	public ConfigMapRefreshAction(ConfigurationMap map) {
		super("Refresh");
		setImageDescriptor(ImageDescriptor.createFromImage(UIPlugin.getImage("refresh_tab.gif")));

		setToolTipText("Refresh");
		configMap = map;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.jface.action.Action#run()
	 */
	@Override
	public void run() {
		super.run();
		configMap.updateElements();
		configMap.refresh();
	}
}
