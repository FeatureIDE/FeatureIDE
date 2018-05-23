/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.deltaj.ui.wizard;

import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.wizard.IWizardPage;
import org.eclipse.ui.wizards.newresource.BasicNewResourceWizard;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.wizardextension.DefaultNewFeatureProjectWizardExtension;
import de.ovgu.featureide.deltaj.DeltajComposer;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Extension of the NewFeatureProjectEditor. Adding pages to import a Feature Model, to select Deltas to be initially creadted and to select whether to create a single file for each Delta.
 * @author Sven Schuster
 */
public class DeltaJNewProjectWizardExtension extends DefaultNewFeatureProjectWizardExtension {
	public static final String ICON_FOLDER = "icons/";
	
	private FinishPage finishPage;
	private ImportModelPage importModelPage;
	private FeatureToDeltaPage featureToDeltaPage;
	private FeatureModel featureModel;
	
	private boolean finished;
	private boolean createsSeperateFiles;
	private Set<String> features;

	private String directoryPath;
	private String modelPath;
	
	private ArrayList<Feature> selectedOptionalFeatures;
	private ArrayList<DOptFeature> combinedOptionalFeatures;
	
	private IProject project;
	private IFolder sourceFolder;
	
	public DeltaJNewProjectWizardExtension() {
		super();
		setFeatures(new HashSet<String>());
		directoryPath = new String();
		finished = false;
		createsSeperateFiles = false;
		setSelectedOptionalFeatures(new ArrayList<Feature>());
		setCombinedOptionalFeatures(new ArrayList<DOptFeature>());
		
		importModelPage = new ImportModelPage(features, directoryPath, this);
		featureToDeltaPage = new FeatureToDeltaPage(featureModel, this);
		finishPage = new FinishPage(this);
	}
	
	@Override
	public boolean isFinished() {
		return this.finished;
	}
	
	private void setFeatures(HashSet<String> features) {
		this.features = features;
	}

	/**
	 * @return the feature model
	 */
	public FeatureModel getModel() {
		return featureModel;
	}
	
	
	@Override
	public IWizardPage getNextPage(IWizardPage page) {
		if (page instanceof FeatureToDeltaPage) {
			return finishPage;
		} else if (page instanceof ImportModelPage) {
			return featureToDeltaPage;
		} else {
			return importModelPage;
		}
	}

	@Override
	public void setWizard(BasicNewResourceWizard wizard) {
		super.setWizard(wizard);
		importModelPage.setWizard(wizard);
		featureToDeltaPage.setWizard(wizard);
		finishPage.setWizard(wizard);
	}
	
	/**
	 * Replaces the initial feature model of FeatureIDE with the imported one.
	 * @throws FileNotFoundException
	 * @throws CoreException
	 */
	protected void replaceModel() throws FileNotFoundException, CoreException {
		IFile modelFile = project.getFile("model.xml");
		FileInputStream stream;
		stream = new FileInputStream(modelPath);
		if(modelFile.exists())
			modelFile.setContents(stream, true, false, null);
		else
			modelFile.create(stream, true, null);
		CorePlugin.getFeatureProject(modelFile).getFeatureModel().handleModelDataChanged();
	}
	
	/**
	 * Creates the initial deltas.
	 * @throws CoreException
	 */
	protected void createDeltas() throws CoreException {
		DeltaJFeatureMapper mapper = new DeltaJFeatureMapper(this.featureModel);
		if(!this.createsSeperateFiles) {
			IFile programFile = this.sourceFolder.getFile(this.featureModel.getRoot().getName()+DeltajComposer.FILE_EXT);
			if(!programFile.exists()){
				InputStream inputstream = new ByteArrayInputStream(mapper.writeProgram(this.selectedOptionalFeatures,this.combinedOptionalFeatures).toByteArray());
				programFile.create(inputstream, false, null);
			}
			IFile splFile = this.project.getFile(DeltajComposer.FILENAME_RULES);
			if(!splFile.exists()) {
				InputStream inputstream = new ByteArrayInputStream(mapper.writeSeperateSpl(this.selectedOptionalFeatures,this.combinedOptionalFeatures).toByteArray());
				splFile.create(inputstream, false, null);
			}
		}
		else {
			for (Feature feature : mapper.getMandatoryEndFeatures()) {
				IFile deltaFile = this.sourceFolder.getFile(feature.getName()+DeltajComposer.FILE_EXT);
				if(!deltaFile.exists()) {
					InputStream inputstream = new ByteArrayInputStream(mapper.writeSeperateModule(feature).toByteArray());
					deltaFile.create(inputstream, false, null);
				}
			}
			for (Feature f : this.selectedOptionalFeatures) {
				IFile deltaFile = this.sourceFolder.getFile(f.getName()+DeltajComposer.FILE_EXT);
				if(!deltaFile.exists()) {
					InputStream inputstream = new ByteArrayInputStream(mapper.writeSeperateModule(f).toByteArray());
					deltaFile.create(inputstream, false, null);
				}
			}
			for(DOptFeature comb : this.combinedOptionalFeatures) {
				IFile deltaFile = this.sourceFolder.getFile(comb.getDeltaModule()+DeltajComposer.FILE_EXT);
				if(!deltaFile.exists()) {
					InputStream inputstream = new ByteArrayInputStream(mapper.writeSeperateCombinedModule(comb).toByteArray());
					deltaFile.create(inputstream, false, null);
				}
			}
			IFile splFile = this.project.getFile(DeltajComposer.FILENAME_RULES);
			if(!splFile.exists()) {
				InputStream inputstream = new ByteArrayInputStream(mapper.writeSeperateSpl(this.selectedOptionalFeatures,this.combinedOptionalFeatures).toByteArray());
				splFile.create(inputstream, false, null);
			}
		}
		this.project.refreshLocal(IResource.DEPTH_INFINITE, null);
	}
	
	@Override
	public void extendedEnhanceProject(IProject project, String compID, String sourcePath, String configPath, String buildPath) {
		this.project = project;
		this.sourceFolder = project.getFolder(sourcePath);
		EnhanceProjectJob epj = new EnhanceProjectJob("Enhance DeltaJ Project", this);
		epj.schedule();
		try {
			epj.join();
		} catch (InterruptedException e) {
			CorePlugin.getDefault().logError(e);
		}
	}

	/**
	 * @return selectedOptionalFeatures
	 */
	public ArrayList<Feature> getSelectedOptionalFeatures() {
		return this.selectedOptionalFeatures;
	}

	/**
	 * @return combinedOptionalFeatures
	 */
	public ArrayList<DOptFeature> getCombinedOptionalFeatures() {
		return this.combinedOptionalFeatures;
	}

	/**
	 * @param combinedOptionalFeatures
	 */
	public void setCombinedOptionalFeatures(ArrayList<DOptFeature> combinedOptionalFeatures) {
		this.combinedOptionalFeatures = combinedOptionalFeatures;
	}

	/**
	 * @param selectedOptionalFeatures
	 */
	public void setSelectedOptionalFeatures(ArrayList<Feature> selectedOptionalFeatures) {
		this.selectedOptionalFeatures = selectedOptionalFeatures;
	}

	/**
	 * @return createsSeperateFiles
	 */
	public boolean isCreatesSeperateFiles() {
		return this.createsSeperateFiles;
	}

	/**
	 * @param createsSeperateFiles
	 */
	public void setCreatesSeperateFiles(boolean createsSeperateFiles) {
		this.createsSeperateFiles = createsSeperateFiles;
	}

	/**
	 * @param finished
	 */
	public void setFinished(boolean finished) {
		this.finished = finished;
	}

	/**
	 * @param modelPath
	 */
	public void setModelPath(String modelPath) {
		this.modelPath = modelPath;
	}

	/**
	 * @param model
	 */
	public void setModel(FeatureModel featureModel) {
		this.featureModel = featureModel;
	}

	/**
	 * @return directoryPath
	 */
	public String getDirectoryPath() {
		return this.directoryPath;
	}
}
