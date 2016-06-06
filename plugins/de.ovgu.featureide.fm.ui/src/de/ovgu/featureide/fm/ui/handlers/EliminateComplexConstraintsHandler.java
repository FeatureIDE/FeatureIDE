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
package de.ovgu.featureide.fm.ui.handlers;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATING_FEATURE_DEPENDENCIES;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collection;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
import org.eclipse.ui.part.FileEditorInput;

import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.conversion.ComplexConstraintConverter;
import de.ovgu.featureide.fm.core.conversion.IConverterStrategy;
import de.ovgu.featureide.fm.core.conversion.NNFConverter;
import de.ovgu.featureide.fm.core.conversion.CNFConverter;
import de.ovgu.featureide.fm.core.io.FMConverter;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.FeatureModelWriterIFileWrapper;
import de.ovgu.featureide.fm.core.io.ProblemList;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.manager.FileHandler;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelFormat;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelWriter;
import de.ovgu.featureide.fm.core.job.SliceFeatureModelJob;
import de.ovgu.featureide.fm.core.job.util.JobArguments;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.handlers.base.AFileHandler;
import de.ovgu.featureide.fm.ui.wizards.AbstractWizard;
import de.ovgu.featureide.fm.ui.wizards.EliminateConstraintsPage;
import de.ovgu.featureide.fm.ui.wizards.EliminateConstraintsWizard;
import de.ovgu.featureide.fm.ui.wizards.FeatureModelConversionWizard;
import de.ovgu.featureide.fm.ui.wizards.FeatureModelSlicingWizard;
import de.ovgu.featureide.fm.ui.wizards.NewFeatureModelWizardPage;
import de.ovgu.featureide.fm.ui.wizards.WizardConstants;

/**
 * TODO description
 * 
 * @author Alexander
 */
public class EliminateComplexConstraintsHandler extends AFileHandler {
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.ui.handlers.base.AFileHandler#singleAction(org.eclipse.core.resources.IFile)
	 */
	@Override
	protected void singleAction(IFile file) {
		final IFeatureModel featureModel = readModel(file);
		
		IConverterStrategy strategy = new NNFConverter();
		final ComplexConstraintConverter converter = new ComplexConstraintConverter();
		
		if(!ComplexConstraintConverter.trivialRefactoring(featureModel)) {
			final EliminateConstraintsWizard wizard = new EliminateConstraintsWizard(file, "Complex-constraints elimination");
			if (Dialog.OK == new WizardDialog(Display.getCurrent().getActiveShell(), wizard).open()) {
				strategy = wizard.getStrategy();
				converter.enablePreserveConfigurations(wizard.preserveConfigurations());
			}
		}
		
		IFeatureModel result = converter.convert(featureModel, strategy);
		
		final FeatureModelWriterIFileWrapper fmWriter = new FeatureModelWriterIFileWrapper(new XmlFeatureModelWriter(result));
		try {
			fmWriter.writeToFile(file);
			file.refreshLocal(IResource.DEPTH_ZERO, null);
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
		try {
			openFileInEditor(file);
		} catch (PartInitException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	
	private void openFileInEditor(IFile outputFile) throws PartInitException {
		final IWorkbenchPage page = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
		final IEditorInput editorInput = new FileEditorInput(outputFile);
		final IEditorReference[] refs = page.getEditorReferences();
		for (int i = 0; i < refs.length; i++) {
			if (refs[i].getEditorInput().equals(editorInput)) {
				page.closeEditor(refs[i].getEditor(false), false);
				break;
			}

		}
		IDE.openEditor(page, outputFile);
	}
	/**
	 * reads the featureModel from file
	 * 
	 * @param inputFile
	 * @return featureModel
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	private IFeatureModel readModel(IFile inputFile) {
		IFeatureModel fm = FMFactoryManager.getFactory().createFeatureModel();
		FeatureModelReaderIFileWrapper fmReader = new FeatureModelReaderIFileWrapper(new XmlFeatureModelReader(fm));

		try {
			fmReader.readFromFile(inputFile);
		} catch (FileNotFoundException e) {
			FMUIPlugin.getDefault().logError(e);
		} catch (UnsupportedModelException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return fm;
	}

}
