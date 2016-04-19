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
package de.ovgu.featureide.deltamontiarc.actions;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.List;

import mc.deltamontiarc.MADeltaTool;
import mc.deltamontiarc._tool.MADeltaRoot;
import mc.helper.NameHelper;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;

import de.ovgu.featureide.deltamontiarc.AnnotationHelper;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.SingleSelectionAction;

public class AnnotateDeltaAction extends SingleSelectionAction {

	public AnnotateDeltaAction(String text, Object viewer2) {
		super(text, viewer2);
	}
	
	@Override
	public void run() {
		FileDialog fileDialog = new FileDialog(new Shell(), SWT.MULTI);
		fileDialog.setFilterExtensions(new String[]{"*.delta", "*.*"});
		fileDialog.setOverwrite(false);

		String filepath = fileDialog.open();
		if (filepath == null)
			return;
		
		String[] fileNames = fileDialog.getFileNames();
		String directory = new File(filepath).getParent();
		for (String fileName : fileNames) {
			
			File inputFile = new File(directory+File.separator+fileName);
			// parse input file and get package structure
			List<String> packageStructure = getPackageStructure(inputFile);
			
			// copy input file into corresponding feature folder
			AnnotationHelper helper = new AnnotationHelper();
			FeatureModelEditor featureModelEditor = helper.getFeatureModelEditor();
			if (featureModelEditor == null) {
				return;
			}
			IProject project = ((IResource) featureModelEditor.getGrammarFile().getResource().getAdapter(IFile.class)).getProject();
			String sourceName = featureModelEditor.getFeatureModel().getProjectConfigurationPath(project);
			IFolder sourceFolder = null;
			if (sourceName != null && !sourceName.equals("")) {
				sourceFolder = project.getFolder(sourceName);
			}
			if (sourceFolder != null) {
				IFolder featureFolder = sourceFolder.getFolder(getSelectedFeature().getName());
				IFolder targetFolder = featureFolder.getFolder(NameHelper.separatedStringFromList(packageStructure, File.separator));
				try {
					if (!targetFolder.exists()) {
						targetFolder.create(true, true, null);
					}
					IFile outputFile = targetFolder.getFile(inputFile.getName());
					InputStream in = new FileInputStream(inputFile);
					outputFile.create(in, true, null);
					in.close();
				} catch (FileNotFoundException e) {
					FMUIPlugin.getDefault().logError(e);
				} catch (IOException e) {
					FMUIPlugin.getDefault().logError(e);
				} catch (CoreException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}	
	}

	private List<String> getPackageStructure(File modelFile) {
		if (modelFile != null) {
            String modelFileName = modelFile.getAbsolutePath();
            String[] args = new String[]{
                    modelFileName,
                    "-analysis", "delta", "parse"
            };
            MADeltaTool tool = new MADeltaTool(args);
            tool.init();
            tool.run();
            MADeltaRoot root = (MADeltaRoot) tool.getModelloader().getRootByFileName(modelFileName);
            if (root != null) {
                return root.getAst().getPackage();
            }
        }
		return null;
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
		setChecked(false);
	}


}
