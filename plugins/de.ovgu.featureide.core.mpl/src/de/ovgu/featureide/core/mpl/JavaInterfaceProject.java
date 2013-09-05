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
package de.ovgu.featureide.core.mpl;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.mpl.io.FileLoader;
import de.ovgu.featureide.core.mpl.signature.FeatureRoles;
import de.ovgu.featureide.core.mpl.signature.RoleMap;
import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.mpl.signature.ViewTagPool;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * Holds all relevant information about the interface project.
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class JavaInterfaceProject {
	private final IProject projectReference;
	private final ViewTagPool viewTagPool = new ViewTagPool();
	
	private ViewTag filterViewTag = null;
	private int configLimit = 1000;
	
	private RoleMap roleMap;
	private Configuration configuration;

	private final FeatureModel featureModel;
	private final IFeatureProject featureProject;
	
	public JavaInterfaceProject(IProject projectReference) {
		this(projectReference, null);
	}
	
	public JavaInterfaceProject(IProject projectReference, IFeatureProject featureProject) {
		this.projectReference = projectReference;
		this.featureProject = featureProject;
		featureModel = FileLoader.loadFeatureModel(this);
		refreshRoleMap();
	}
	
	
	// TODO FujiTest
	public void refreshRoleMap() {
		if (featureProject == null) {
			MPLPlugin.getDefault().logInfo("Try to load RoleMap from local files...");
			roleMap = FileLoader.loadRoleMap(this);
		} else {
			// TODO FujiTest
//			roleMap = new JavaSignatureWriter(featureProject, this).writeSignatures();
			MPLPlugin.getDefault().logInfo("Try to load RoleMap from fuji...");
			roleMap = FileLoader.fuijTest(this, featureProject);
		}
	}
	
	public RoleMap getRoleMap() {
		return roleMap;
	}

	public FeatureRoles getRoles(String featurename) {
		return roleMap.getRoles(featurename);
	}

	public IProject getProjectReference() {
		return projectReference;
	}
	
	public FeatureModel getFeatureModel() {
		return featureModel;
	}
	
	public int getConfigLimit() {
		return configLimit;
	}
	
	public Configuration getConfiguration() {
		if (configuration == null) {
			configuration = FileLoader.loadConfiguration(this);
		}
		return configuration;
	}

	public void setConfiguration(Configuration configuration) {
		this.configuration = configuration;
	}
	
	public ViewTag getFilterViewTag() {
		return filterViewTag;
	}
	
	public ViewTagPool getViewTagPool() {
		return viewTagPool;
	}

	public void setConfigLimit(int configLimit) {
		this.configLimit = configLimit;
	}
	
	public void setFilterViewTag(ViewTag filterViewTag) {
		this.filterViewTag = filterViewTag;
	}
	
	public void setFilterViewTag(String viewName, int viewLevel) {
		if (viewName != null) {
			this.filterViewTag = new ViewTag(viewName, viewLevel);
		}
	}
	
	public void clearFilterViewTag() {
		this.filterViewTag = null;
	}
	
	public void scaleUpViewTag(String name, int level) {
		viewTagPool.scaleUpViewTags(name, level);
	}
	
	public void removeViewTag(String name) {
		viewTagPool.removeViewTag(name);
	}
}
