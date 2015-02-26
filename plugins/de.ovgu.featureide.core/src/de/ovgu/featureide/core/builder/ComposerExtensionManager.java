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
package de.ovgu.featureide.core.builder;

import java.util.List;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.ExtensionPointManager;
import de.ovgu.featureide.core.IFeatureProject;


/**
 * Manages the FeatureIDE extensions to compose features.
 * 
 * @author Tom Brosch
 * @author Stefan Krueger
 * @author Sebastian Krieter
 */
public class ComposerExtensionManager extends ExtensionPointManager<IComposerExtension> {

	private static ComposerExtensionManager instance = new ComposerExtensionManager();

	ComposerExtensionManager() {
		super(CorePlugin.PLUGIN_ID, IComposerExtension.extensionPointID);
	}
	
	public static ComposerExtensionManager getInstance() {
		return instance;
	}

	@Override
	protected IComposerExtension parseExtension(
			IConfigurationElement configurationElement) {
		if (!IComposerExtension.extensionID.equals(configurationElement.getName()))
			return null;
		return new ComposerExtensionProxy(configurationElement);
	}
	
	public List<IComposerExtension> getComposers() {
		return getProviders();
	}
	
	/**
	 * Gets a composer by an ID
	 * 
	 * @param composerID The ID of the composer
	 * @return The composer or null if no composer with the specified ID was found
	 */
	public IComposerExtensionClass getComposerById(IFeatureProject featureProject, String composerID) {
		for (IComposerExtension tool : getComposers()) {
			if (tool.getId().equals(composerID)) {
				return tool.getComposerByProject(featureProject);	
			}
		}
		return null;
	}
	
	public IStatus isComposerInstalled(IProjectDescription desc){		
		for (ICommand iCommand : desc.getBuildSpec()) {
			if(iCommand.getBuilderName().compareTo("de.ovgu.featureide.core.extensibleFeatureProjectBuilder") == 0){
				String composerName = iCommand.getArguments().get("composer");
				for (IComposerExtension tool : getComposers()) {
					if(tool.getId().equals(composerName)){
						return tool.getComposerByProject(null).areDependentPluginsInstalled(desc);
					}
				}
				return new Status(Status.ERROR, "unknown", Status.ERROR, "The required composer "+composerName+" is not supported.", null);
			}
		}
		return new Status(Status.ERROR, "unknown", Status.ERROR, "The description does not contain a composer ID.", null);
	}	
}
