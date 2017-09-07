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
package de.ovgu.featureide.cmake;

import static de.ovgu.featureide.fm.core.localization.StringTable.IS_NOT_INSTALLED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.THE_REQUIRED_BUNDLE;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.cdt.core.CCorePlugin;
import org.eclipse.cdt.core.cdtvariables.ICdtVariableManager;
import org.eclipse.cdt.core.envvar.IEnvironmentContributor;
import org.eclipse.cdt.core.envvar.IEnvironmentVariable;
import org.eclipse.cdt.core.envvar.IEnvironmentVariableManager;
import org.eclipse.cdt.core.model.CoreModel;
import org.eclipse.cdt.core.settings.model.ICBuildSetting;
import org.eclipse.cdt.core.settings.model.ICConfigurationDescription;
import org.eclipse.cdt.core.settings.model.ICOutputEntry;
import org.eclipse.cdt.core.settings.model.ICProjectDescription;
import org.eclipse.cdt.core.settings.model.ICSettingContainer;
import org.eclipse.core.resources.IBuildConfiguration;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IPathVariableManager;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;

import de.ovgu.featureide.cmake.wrapper.CMakeWrapper;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.io.manager.ConfigurationManager;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;

/**
 * A FeatureIDE extension to compose FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class CMakeComposer extends ComposerExtensionClass {
	private static final String PLUGIN_ID = "org.eclipse.cdt";
	private static final String PLUGIN_WARNING = THE_REQUIRED_BUNDLE+PLUGIN_ID+IS_NOT_INSTALLED_;
	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.cmake";
	public static final String C_NATURE = "org.eclipse.cdt.core.cnature";
	public static final String CC_NATURE = "org.eclipse.cdt.core.ccnature";

	 private final String CMAKE_OPTION_PATTERN = "set(%s %s CACHE BOOL \"\" FORCE)\n";
	 private final String CMALE_OPTION_ENABLED = "ON";
	 private final String CMALE_OPTION_DISABLED = "OFF";
	 private final String FEATUREIDE_LATEST_CMAKE_BUILD_FODLER = "FEATUREIDE_LATEST_CMAKE_BUILD_FODLER"; 
	 
	 private IFolder buildFolder;
	private final CMakeWrapper cMakeWrapper = new CMakeWrapper();
	private String configName;
	
	public boolean initialize(IFeatureProject project) {
		super.initialize(project);		
		buildFolder = CorePlugin.createFolder(project.getProject(), "build");
		cMakeWrapper.initialize(project.getBuildFolder(), buildFolder);
		return true;
	}

	
	public void performFullBuild(IFile config) {
		if(!isPluginInstalled(PLUGIN_ID)){
			featureProject.createBuilderMarker(featureProject.getProject(), PLUGIN_WARNING, -1, IMarker.SEVERITY_ERROR);
		}
		if (!isInitialized()) {
			final IFeatureProject configFeatureProject = CorePlugin.getFeatureProject(config);
			if (configFeatureProject == null) {
				return;
			}
			initialize(configFeatureProject);
		}
		
		evaluateCurrentConfigName();
		IFile file = composeCMakeConfFile();
				
		if(file != null)
		{
			setBuildDirectoryForCurrentConfiguration();
			cMakeWrapper.run(file);
		}
	}
	
	/**
	 * 
	 */
	private void setBuildDirectoryForCurrentConfiguration() {
		try {
			// set path variable
			IPath pathToBuildFolder = buildFolder.getFolder(configName).getLocation();			
			ICProjectDescription prjDesc = CoreModel.getDefault().getProjectDescription(featureProject.getProject()); 
			ICConfigurationDescription cfgDesc = prjDesc.getActiveConfiguration(); 				
			ICBuildSetting buildSetting = cfgDesc.getBuildSetting();

			buildSetting.setBuilderCWD(pathToBuildFolder);
			
			CoreModel.getDefault().setProjectDescription(featureProject.getProject(),prjDesc);
		} catch (CoreException e) {
			CMakeCorePlugin.getDefault().logError(e);
		}
	}
	
	/**
	 * 
	 */
	private IFile composeCMakeConfFile() {
		IFile retval = null;
		final Configuration configuration = readConfig();		
				
		// create build folder for this selected configuration
		IFolder folder = buildFolder.getFolder(configName);		
		if(!folder.exists())
		{
			try {
				folder.create(IResource.NONE, true, null);
			} catch (CoreException e) {
				CMakeCorePlugin.getDefault().logError(e);
			}
		}
		
		
		// Generate content
		String configString = "# Autogenerated by FeatureIDE CMake Composer Plugin \n \n";
		for (final SelectableFeature f : configuration.getFeatures()) {
			if (!f.getFeature().getStructure().isAbstract()) {
				configString += String.format(CMAKE_OPTION_PATTERN
												, f.getFeature().getName().toUpperCase().replace(' ', '_')
												, f.getSelection() == Selection.SELECTED ? CMALE_OPTION_ENABLED : CMALE_OPTION_DISABLED);														
			}
		}
		
		// Write to file
		InputStream inputStream = new ByteArrayInputStream(configString.getBytes(StandardCharsets.UTF_8));
		IFile file = folder.getFile(configName + ".cmake");
		try {
			if(!file.exists())
			{
				createFile(file, inputStream);
			}
			else
			{
				file.setContents(inputStream, IResource.FORCE, null);
			}
			retval = file;
		} catch (CoreException e) {
			CMakeCorePlugin.getDefault().logError(e);
		}
		
		return retval;
	}


	/**
	 * 
	 */
	private void evaluateCurrentConfigName() {
		configName = featureProject.getCurrentConfiguration().getName();
		configName = configName.substring(0, configName.length() - getConfigurationExtension().length() - 1);
	}


	private void createFile(final IFile file, final InputStream stream) throws CoreException {
		if (file != null) {
			file.create(stream, true, null);
		}
	}
	
	/**
	 * Reads and returns current feature config.
	 * 
	 * @return
	 */
	private Configuration readConfig() {
		final Configuration featureProjectConfig = new Configuration(featureProject.getFeatureModel());
		final java.nio.file.Path configPath = java.nio.file.Paths.get(featureProject.getCurrentConfiguration().getLocationURI());
		FileHandler.load(configPath, featureProjectConfig, ConfigurationManager.getFormat(configPath.getFileName().toString()));

		return featureProjectConfig;
	}



	@Override
	public void addCompiler(IProject project, String sourcePath,
			String configPath, String buildPath) {
		addNature(project);
	}
	
	private void addNature(IProject project) {
		try {
			if (!project.isAccessible())
				return;
			
			int i = 2;
			if (project.hasNature(C_NATURE)) {
				i--;
			}
			if (project.hasNature(CC_NATURE)) {
				i--;
			}
			if (i == 0) {
				return;
			}
			IProjectDescription description = project.getDescription();
			String[] natures = description.getNatureIds();
			String[] newNatures = new String[natures.length + i];
			System.arraycopy(natures, 0, newNatures, 0, natures.length);
			if (project.hasNature(C_NATURE)) {
				newNatures[natures.length] = CC_NATURE;
			} else if (project.hasNature(CC_NATURE)) {
				newNatures[natures.length] = C_NATURE;
			} else {
				newNatures[natures.length] = C_NATURE;
				newNatures[natures.length + 1] = CC_NATURE;
			}
			description.setNatureIds(newNatures);
			project.setDescription(description, null);
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	
	@Override
	public String replaceSourceContentMarker(String text,  boolean refines, String packageName) {
		if (refines)
			text = text.replace(REFINES_PATTERN, "refines");
		else
			text = text.replace(REFINES_PATTERN + " ", "");
		return super.replaceSourceContentMarker(text, refines, packageName);
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#refines()
	 */
	@Override
	public boolean refines() {
		return true;
	}

	@Override
	public void postCompile(IResourceDelta delta, IFile file) {
		super.postCompile(delta, file);
		try {
			file.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			CMakeCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public String getConfigurationExtension() {
		return "config";
	}

	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String configurationName) {
		super.buildConfiguration(folder, configuration, configurationName);
		cMakeWrapper.initialize(null, folder);
		try {
			for (IResource res : folder.members()) {
				if (res instanceof IFile && getConfigurationExtension().equals(res.getFileExtension())) {
					//cMakeWrapper.composeCmakeConfFile((IFile)res);
				}
			}
		} catch (CoreException e) {
			CMakeCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public Mechanism getGenerationMechanism() {
	    return IComposerExtensionClass.Mechanism.FEATURE_ORIENTED_PROGRAMMING;
	}


	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.IComposerExtensionBase#supportsMigration()
	 */
	@Override
	public boolean supportsMigration()
	{
		return false;
	}
	
	public boolean hasFeatureFolder()
	{
		return false;
	}

}
