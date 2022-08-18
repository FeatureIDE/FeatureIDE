/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core;

import static de.ovgu.featureide.fm.core.localization.StringTable.THEOREM_PROVING;
import static de.ovgu.featureide.fm.core.localization.StringTable.VARIABILITY_AWARE_TESTING;

import java.nio.file.Path;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.QualifiedName;

import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;

public interface IFeatureProject extends IBuilderMarkerHandler {

	QualifiedName composerConfigID = new QualifiedName("featureproject.configs", "composer");

	String SOURCE_ARGUMENT = "source";
	String CONFIGS_ARGUMENT = "equations";
	String BUILD_ARGUMENT = "build";

	QualifiedName buildFolderConfigID = new QualifiedName("featureproject.configs", BUILD_ARGUMENT);
	QualifiedName configFolderConfigID = new QualifiedName("featureproject.configs", CONFIGS_ARGUMENT);
	QualifiedName sourceFolderConfigID = new QualifiedName("featureproject.configs", SOURCE_ARGUMENT);
	QualifiedName compositionMechanismConfigID = new QualifiedName("featureproject.configs", "compositionmechanism");

	@Deprecated
	String DEFAULT_SOURCE_PATH = "src";
	@Deprecated
	String DEFAULT_CONFIGS_PATH = "equations";
	@Deprecated
	String DEFAULT_BUILD_PATH = "build";
	String DEFAULT_CONTRACT_COMPOSITION = "None";

	// TODO revise with enum
	String META_THEOREM_PROVING = THEOREM_PROVING;
	String META_MODEL_CHECKING = "Model Checking (JPF-core)";
	String META_MODEL_CHECKING_BDD_JAVA_JML = "Model Checking (JPF-BDD Java JML)";
	String META_VAREXJ = VARIABILITY_AWARE_TESTING;
	String META_MODEL_CHECKING_BDD_JAVA = "Model Checking (JPF-BDD Java)";
	String META_MODEL_CHECKING_BDD_C = "Model Checking (JPF-BDD C)";

	String DEFAULT_COMPOSITION_MECHANISM = "Mixin";
	QualifiedName configConfigID = new QualifiedName("featureproject.configs", "currentEquation");

	QualifiedName javaClassPathID = new QualifiedName("featureproject.configs", "javaClassPath");
	QualifiedName contractCompositionID =
		new QualifiedName(IFeatureProject.class.getName() + "#ContractComposition", IFeatureProject.class.getName() + "#ContractComposition");

	String MARKER_NEVER_SELECTED = "Never-selected: ";
	String MARKER_ALWAYS_SELECTED = "Always-selected: ";

	void dispose();

	String getProjectName();

	/**
	 *
	 * @return The current configuration file or <code>null</code> if there is none.
	 */
	Path getCurrentConfiguration();

	Configuration loadCurrentConfiguration();

	Configuration loadConfiguration(Path configurationPath);

	void setCurrentConfiguration(Path file);

	String getBuildPath();

	IFolder getBinFolder();

	IFolder getLibFolder();

	IFolder getBuildFolder();

	IFolder getConfigFolder();

	IFolder getSourceFolder();

	String getBinPath();

	String getConfigPath();

	String getSourcePath();

	String getFeaturestubPath();

	String[] getJavaClassPath();

	String getContractComposition();

	String getMetaProductGeneration();

	String getCompositionMechanism();

	/**
	 * Gets the java class path without the default paths
	 *
	 * @return The java class path without default paths
	 */
	String[] getAdditionalJavaClassPath();

	/**
	 * Returns the name of the feature this resource belongs to, or <code>null</code> if the resource does not belong to any feature in this project
	 *
	 * @param resource resource
	 * @return name of the feature
	 */
	String getFeatureName(IResource resource);

	String getConfigName(IResource resource);

	String getFolderName(IResource resource, IFolder folder);

	IProject getProject();

	ProjectSignatures getProjectSignatures();

	FSTModel getFSTModel();

	// TODO _Refactor: remove
	IFeatureModel getFeatureModel();

	IFeatureModelManager getFeatureModelManager();

	IFile getModelFile();

	Path getInternalConfigurationFile();

	Path getInternalConfigurationFile(Path configurationFile);

	/**
	 * Returns the ID of the assigned composer
	 *
	 * @return The ID of the assigned composer or @code null if no composer has been assigned.
	 */
	String getComposerID();

	/**
	 * Sets the ID of the assigned composer
	 *
	 * @param composerID id of the composer to set
	 */
	void setComposerID(String composerID);

	/**
	 * Gets the current composer.
	 *
	 * @return The composer, specified for this project or <code>null</code> if the composerID is unknown <br> - The composer is now a property of the project
	 *         and not specified by the nature or builder (every project has the same nature and builder, which can be extended by other eclipse plug-ins)
	 */
	IComposerExtensionClass getComposer();

	/**
	 * Sets the JAVA class path that is in order to build the project
	 *
	 * @param paths An array of paths that will be added to the JAVA class path
	 */
	void setAdditionalJavaClassPath(String[] paths);

	/**
	 * @param model fst model to set
	 */
	void setFSTModel(FSTModel model);

	/**
	 * sets the contract composition mechanism
	 *
	 * @param contractComposition contract composition mechanism to set
	 */
	void setContractComposition(String contractComposition);

	/**
	 * sets the meta product generation mechanism.
	 *
	 * @param metaProductGeneration meta product generation mechanism to set
	 */
	void setMetaProductGeneration(String metaProductGeneration);

	/**
	 * sets the composition mechanism
	 *
	 * @param compositionMechanism composition mechanism to set
	 */
	void setCompositionMechanism(String compositionMechanism);

	/**
	 * @return True if a source file, or the current configuration changed.
	 */
	boolean buildRelevantChanges();

	void built();

	String getProjectConfigurationPath();

	String getProjectBuildPath();

	String getProjectSourcePath();

	void setPaths(String feature, String src, String configuration);

	List<Path> getAllConfigurations();

	Collection<String> getFalseOptionalConfigurationFeatures();

	Collection<String> getUnusedConfigurationFeatures();

	void checkForProblems();

}
