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
package de.ovgu.featureide.core.builder;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;


/**
 * Handles a composer extension.
 * 
 * @author Tom Brosch
 */
public class ComposerExtensionProxy implements IComposerExtension {
	
	private final IConfigurationElement configElement;
	private final String name;
	private final String id;
	private final String description;
	private IComposerExtensionClass composerExtensionClass = null;

	public ComposerExtensionProxy(IConfigurationElement configurationElement) {
		this.configElement = configurationElement;
		name = configElement.getAttribute("name");
		id = configElement.getAttribute("id");
		description = configElement.getAttribute("description");
	
	}

	public String getName() {
		return name;
	}

	public String getId() {
		return id;
	}

	public String toString() {
		return "Name: " + name + "; ID: " + id;
	}

	public void loadComposerExtension() {
		if (composerExtensionClass != null)
			return;
		try {
			composerExtensionClass = (IComposerExtensionClass) configElement
					.createExecutableExtension("class");
		} catch (CoreException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	public boolean initialize(IFeatureProject project) {
		FeatureModel featureModel = project.getFeatureModel();
		if(featureModel==null||featureModel.getRoot()==null){
			return false;
		}
		loadComposerExtension();
		return composerExtensionClass.initialize(project);
		
	}

	public void performFullBuild(IFile config) {
		CorePlugin.getDefault().logInfo(
				"Perform a full build for configuration '" + config + "'");
		initialize(CorePlugin.getFeatureProject(config));
		composerExtensionClass.performFullBuild(config);
	}

	public String getDescription() {
		return description;
	}

	public boolean clean() {
		loadComposerExtension();
		return composerExtensionClass.clean();
	}

	public LinkedHashSet<String> extensions() {
		return composerExtensionClass.extensions();
	}

	public void copyNotComposedFiles(Configuration config, IFolder destination) {
		composerExtensionClass.copyNotComposedFiles(config, destination);
	}

	public boolean postAddNature(IFolder source, IFolder destination) {
		return composerExtensionClass.postAddNature(source, destination);
	}

	public void buildFSTModel() {
		loadComposerExtension();
		composerExtensionClass.buildFSTModel();
	}

	public ArrayList<String[]> getTemplates(){
		return composerExtensionClass.getTemplates();
	}

	public String replaceSourceContentMarker(String text,  boolean refines, String packageName) {
		return composerExtensionClass.replaceSourceContentMarker(text, refines, packageName);
	}

	public void postCompile(IResourceDelta delta, IFile file) {
		composerExtensionClass.postCompile(delta, file);
	}

	public void addCompiler(IProject project, String sourcePath,String configPath, String buildPath) {
		composerExtensionClass.addCompiler(project, sourcePath, configPath, buildPath);
		
	}
	public boolean hasFeatureFolders(){
		loadComposerExtension();
		return composerExtensionClass.hasFeatureFolders();
	}

	public int getDefaultTemplateIndex() {
		return composerExtensionClass.getDefaultTemplateIndex();
	}

	public void postModelChanged() {
		composerExtensionClass.postModelChanged();
	}

	public boolean hasCustomFilename() {
		return composerExtensionClass.hasCustomFilename();
	}

	public boolean hasFeatureFolder() {
		return composerExtensionClass.hasFeatureFolder();
	}

	public String getConfigurationExtension() {
		return composerExtensionClass.getConfigurationExtension();
	}

	public void buildConfiguration(IFolder folder, Configuration configuration, String congurationName) {
		composerExtensionClass.buildConfiguration(folder, configuration, congurationName);
	}
	
	public boolean preBuildConfiguration() {
		return composerExtensionClass.preBuildConfiguration();
	}

	public boolean refines() {
		return composerExtensionClass.refines();
	}

	public boolean hasSourceFolder() {
		return composerExtensionClass.hasSourceFolder();
	}

	public boolean canGeneratInParallelJobs() {
		return composerExtensionClass.canGeneratInParallelJobs();
	}

	public boolean showContextFieldsAndMethods() {
		return composerExtensionClass.showContextFieldsAndMethods();
	}

	public LinkedList<FSTDirective> buildModelDirectivesForFile(Vector<String> lines) {
		return composerExtensionClass.buildModelDirectivesForFile(lines);
	}

	public boolean needColor() {
		return composerExtensionClass.needColor();
	}

	public boolean hasContractComposition() {
		return composerExtensionClass.hasContractComposition();
	}

	public boolean hasMetaProductGeneration() {
		return composerExtensionClass.hasMetaProductGeneration();
	}

	public boolean hasCompositionMechanisms() {
		return composerExtensionClass.hasCompositionMechanisms();
	}

	public Mechanism getGenerationMechanism() {
	    return composerExtensionClass.getGenerationMechanism();
	}
}
