/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.featurecpp;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.nio.charset.Charset;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.builder.ComposerExtensionClass;
import de.ovgu.featureide.featurecpp.model.FeatureCppModelBuilder;
import de.ovgu.featureide.featurecpp.wrapper.FeatureCppWrapper;
import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * A FeatureIDE extension to compose FeatureC++ files.
 * 
 * @author Tom Brosch
 * @author Jens Meinicke
 */
public class FeatureCppComposer extends ComposerExtensionClass {

	public static final String COMPOSER_ID = "de.ovgu.featureide.composer.featurecpp";
	public static final String C_NATURE = "org.eclipse.cdt.core.cnature";
	public static final String CC_NATURE = "org.eclipse.cdt.core.ccnature";

	/**
	 * This wrapper builds the current configuration into the build folder.
	 */
	private final FeatureCppWrapper featureCpp = new FeatureCppWrapper();
	
	/**
	 * This wrapper builds a complete configuration into the temp folder to 
	 * generate a full FST model.
	 */
	private final FeatureCppWrapper featureCppModelWrapper = new FeatureCppWrapper();
	
	/**
	 * This folder called FSTModel is the location where the model wrapper will build the full configuration.
	 */
	private IFolder tempFolder;
	
	/**
	 * This folder called .tmp contains the full configuration and the temp folder.
	 */
	private IFolder parentFolder;
	
	private FeatureCppModelBuilder featureCppModelBuilder;
	

	public boolean initialize(IFeatureProject project) {
		if (project == null) {
			return false;
		}
		super.initialize(project);
		featureCpp.initialize(project.getSourceFolder(), project.getBuildFolder());
		createTempFolder();
		
		featureCppModelWrapper.initialize(project.getSourceFolder(), tempFolder);
		
		if (featureCppModelBuilder == null) {
			featureCppModelBuilder = new FeatureCppModelBuilder(project, tempFolder);
			buildFSTModel();
		}
		return true;
	}


	/**
	 * Creates the folders for building a full FST model.<br>
	 * {@link FeatureCppComposer#parentFolder}<br>
	 * {@link FeatureCppComposer#tempFolder}
	 */
	private void createTempFolder() {
		parentFolder = featureProject.getProject().getFolder(".tmp");
		if (!parentFolder.exists()) {
			try {
				parentFolder.create(true, true, null);
				parentFolder.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
		}
		
		tempFolder = parentFolder.getFolder("FSTModel");
		if (!tempFolder.exists()) {
			try {
				tempFolder.create(true, true, null);
				tempFolder.refreshLocal(IResource.DEPTH_ZERO, null);
			} catch (CoreException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
		}
	}


	public void performFullBuild(IFile config) {
		initialize(CorePlugin.getFeatureProject(config));
		featureCpp.compose(config);
		buildFSTModel();
	}

	private static final LinkedHashSet<String> EXTENSIONS = createExtensions(); 
	
	private static LinkedHashSet<String> createExtensions() {
		LinkedHashSet<String> extensions = new LinkedHashSet<String>();
		extensions.add("h");
		return extensions;
	}  

	@Override
	public LinkedHashSet<String> extensions() {
		return EXTENSIONS;
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
	public ArrayList<String[]> getTemplates() {
		return TEMPLATES;
	}
	
	private static final ArrayList<String[]> TEMPLATES = createTempltes();
	
	private static ArrayList<String[]> createTempltes() {
		 ArrayList<String[]> list = new  ArrayList<String[]>(1);
		 list.add(new String[]{"C++", "h", "\r\n" + REFINES_PATTERN + " class " + CLASS_NAME_PATTERN + " {\r\n\r\n};"});
		 return list;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#replaceMarker(java.lang.String, java.util.List)
	 */
	@Override
	public String replaceMarker(String text, List<String> list, String packageName) {
		if (list != null && list.contains("refines"))
			text = text.replace(REFINES_PATTERN, "refines");
		else
			text = text.replace(REFINES_PATTERN + " ", "");
		return text;
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
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}

	@Override
	public String getConfigurationExtension() {
		return "equation";
	}

	@Override
	public void buildFSTModel() {
		if (!tempFolder.exists()) {
			createTempFolder();
		} else {
			try {
				for (IResource res : tempFolder.members()) {
					res.delete(true, null);
				}
				tempFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
		}
		
		
		if (featureProject != null && featureProject.getProject() != null) {
			featureCppModelBuilder.resetModel();
			StringBuilder stringBuilder = new StringBuilder();
			for (String name : featureProject.getFeatureModel().getConcreteFeatureNames()) {
				stringBuilder.append(name);
				stringBuilder.append("\r\n");
			}
			
			InputStream source = new ByteArrayInputStream(stringBuilder.toString()
					.getBytes(Charset.availableCharsets().get("UTF-8")));
			
			IFile file = parentFolder.getFile("." + getConfigurationExtension());
			try {
				if (file.exists()) {
					file.setContents(source, false, true, null);	
				} else {
					file.create(source, true, null);
				}
			} catch (CoreException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
			featureCppModelWrapper.compose(file);
			try {
				tempFolder.refreshLocal(IResource.DEPTH_INFINITE, null);
			} catch (CoreException e) {
				FeatureCppCorePlugin.getDefault().logError(e);
			}
			featureCppModelBuilder.buildModel();
		}
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.builder.ComposerExtensionClass#buildConfiguration(org.eclipse.core.resources.IFolder, de.ovgu.featureide.fm.core.configuration.Configuration)
	 */
	@Override
	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		super.buildConfiguration(folder, configuration, congurationName);
		featureCpp.initialize(null, folder);
		try {
			for (IResource res :folder.members()) {
				if (res instanceof IFile && getConfigurationExtension().equals(res.getFileExtension())) {
					featureCpp.compose((IFile)res);
				}
			}
		} catch (CoreException e) {
			FeatureCppCorePlugin.getDefault().logError(e);
		}
	}
}
