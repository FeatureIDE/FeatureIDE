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

import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.mpl.io.ExtendedConfigurationReader;
import de.ovgu.featureide.core.mpl.io.constants.IOConstants;
import de.ovgu.featureide.core.mpl.io.parser.InterfaceParser;
import de.ovgu.featureide.core.mpl.signature.ViewTag;
import de.ovgu.featureide.core.mpl.signature.ViewTagPool;
import de.ovgu.featureide.core.mpl.signature.java.JavaRoleMap;
import de.ovgu.featureide.core.mpl.signature.java.JavaRoleSignature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;

/**
 * Holds all relevant information about the interface project.
 * 
 * @author Sebastian Krieter
 * @author Reimar Schroeter
 */
public class JavaInterfaceProject {
	private final IProject projectHandle;
	private final ViewTagPool viewTagPool = new ViewTagPool();
	
	private ViewTag filterViewTag = null;
	private int configLimit = 1000;
	
	private JavaRoleMap roleMap = null;
	private Configuration configuration = null;
	private FeatureModel featureModel = null;

	public JavaInterfaceProject(IProject projectHandle) {
		this.projectHandle = projectHandle;
	}
	
	private void loadConfiguration() {
		try {
			ExtendedConfigurationReader exConfReader = new ExtendedConfigurationReader(this);
			configuration = exConfReader.read();
		} catch (Exception e) {
			MPLPlugin.getDefault().logError(e);
		}
	}
	
	private void loadFeatureModel() {
		try {
			featureModel = new FeatureModel();
			XmlFeatureModelReader reader = new XmlFeatureModelReader(featureModel);
			reader.readFromFile(projectHandle.getFile(IOConstants.FILENAME_MODEL).getLocation().toFile());
		} catch (Exception e) {
			featureModel = null;
			MPLPlugin.getDefault().logError(e);
		}
	}
	
	private void loadRoleMap() {		
		roleMap = new JavaRoleMap(this);
		try {
			IFolder mainFolder = projectHandle.getFolder(IOConstants.FOLDERNAME_FEATURE_ROLES);
			if (mainFolder.isAccessible()) {
				InterfaceParser parser = new InterfaceParser(viewTagPool);
				
				for (IResource featureFolder : mainFolder.members()) {
					if (featureFolder instanceof IFolder) {
						for (IResource featureFolderMember : ((IFolder)featureFolder).members()) {
							if (featureFolderMember instanceof IFolder) {
								IFolder packageFolder = (IFolder) featureFolderMember;
								parser.setFeatureName(featureFolder.getName());
								for (IResource file : packageFolder.members()) {
									parser.setFile((IFile)file);
									roleMap.addRole(parser.read());
								}
							} else if (featureFolderMember instanceof IFile) {
								parser.setFile((IFile) featureFolderMember);
								roleMap.addRole(parser.read());
							}
						}	
					}
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
		}
	}
	
	public void refreshRoleMap() {
		loadRoleMap();
	}
	
	public JavaRoleMap getRoleMap() {
		if (roleMap == null) {
			loadRoleMap();
		}
		return roleMap;
	}

	public LinkedList<JavaRoleSignature> getRoles(String featurename) {
		return roleMap.getRoles(featurename);
	}

	public IProject getProject() {
		return projectHandle;
	}

	public Configuration getConfiguration() {
		if (configuration == null) {
			loadConfiguration();
		}
		return configuration;
	}
	
	public FeatureModel getFeatureModel() {
		if(featureModel == null){
			loadFeatureModel();
		}
		return featureModel;
	}
	
	public int getConfigLimit() {
		return configLimit;
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

	public void setRoleMap(JavaRoleMap roleMap) {
		this.roleMap = roleMap;
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
