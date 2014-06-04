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
package de.ovgu.featureide.fm.ui.actions;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;

import de.ovgu.featureide.fm.core.FeatureDependencies;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * calculates and shows dependencies between features in a MessageBox
 * 
 * @author Fabian Benduhn
 */
public class FeatureDependenciesAction implements IObjectActionDelegate {
	private ISelection selection;

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	public void run(IAction action) {
		if (!(selection instanceof IStructuredSelection))
			return;

		Iterator<?> it = ((IStructuredSelection) selection).iterator();
		Object element = it.next();
		IFile inputFile = getInputFile(element);
		if (inputFile == null)
			return;

		final FeatureModel mod = readModel(inputFile);
		Job job = new Job("Calculating Feature Dependencies") {
			protected IStatus run(IProgressMonitor monitor) {
				final String text = new FeatureDependencies(mod).toStringWithLegend();
				// UI access
				final StringBuilder path = new StringBuilder();
				Display.getDefault().syncExec(new Runnable() {

					@Override
					public void run() {
						path.append(openFileDialog());
					}

				});
				saveFile(text, path.toString());
				return Status.OK_STATUS;
			}

		};

		job.setPriority(Job.INTERACTIVE);
		job.schedule();

	}
/**
 * saves the given content to a text File at a given path(including filename)
 * @param content
 * @param path
 */
	private void saveFile(String content, String path) {
		if (path == null)
			return;
		File outputFile = new File(path);
		BufferedWriter out = null;
		try {
			out = new BufferedWriter(new FileWriter(outputFile));
			out.write(content);
		} catch (IOException e) {
		} finally {
			if (out != null) {
				try {
					out.close();
				} catch (IOException e) {
					FMUIPlugin.getDefault().logError(e);
				}
			}
		}
		
		return;
	}

	/**
	 * opens a File Dialog and returns the selected path
	 * 
	 * @param text
	 * 
	 */
	private String openFileDialog() {
		FileDialog fileDialog = new FileDialog(new Shell(), SWT.SAVE);
		fileDialog.setFileName("*.txt");
		fileDialog.setOverwrite(true);
		return fileDialog.open();

	}



	/**
	 * reads the featureModel from file
	 * 
	 * @param inputFile
	 * @return featureModel
	 * @throws UnsupportedModelException
	 * @throws FileNotFoundException
	 */
	private FeatureModel readModel(IFile inputFile) {
		FeatureModel fm = new FeatureModel();
		//XmlFeatureModelReader fmReader = new XmlFeatureModelReader(fm,inputFile.getProject());
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

	/**
	 * gets the feature model file
	 * 
	 * @param element
	 *            the element that is selected when the action is performed
	 * @return
	 */
	private IFile getInputFile(Object element) {
		IFile inputFile = null;
		if (element instanceof IFile) {
			inputFile = (IFile) element;
		} else if (element instanceof IAdaptable) {
			inputFile = (IFile) ((IAdaptable) element).getAdapter(IFile.class);
		}
		return inputFile;
	}

	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

}
