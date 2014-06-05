/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.util;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.io.writer.ExtendedConfigurationWriter;
import de.ovgu.featureide.fm.ui.editors.configuration.ConfigurationEditor;

/**
 * Only for the {@link ConfigurationEditor} <br>
 * taps the {@link Configuration} when the editor is saved.
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationChangeListener implements IPropertyListener {
	@Override
	public void propertyChanged(Object source, int propId) {
		if (propId == IEditorPart.PROP_DIRTY) {
			ConfigurationEditor confEditor = (ConfigurationEditor) source;
			
			if (!confEditor.isDirty()) {
				InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(confEditor.file.getProject());
				
				if (interfaceProject != null) {
					interfaceProject.setConfiguration(confEditor.configuration);
					(new ExtendedConfigurationWriter(interfaceProject)).writeConfiguration();
				}
			}
		}
	}
}
