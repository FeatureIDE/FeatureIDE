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
package de.ovgu.featureide.fm.ui.actions;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.Set;
import java.util.TreeSet;

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
import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * calculates and shows dependencies between features in a MessageBox
 * 
 * @author Fabian Benduhn
 */
public class FeatureDependenciesAction implements IObjectActionDelegate {

	private static String sep = System.getProperty("line.separator");
	private static final String LEGEND_TEXT = "X ALWAYS Y := If X is selected Y is selected in every valid configuration."
			+ sep
			+ "X MAYBE Y   := If X is selected Y is selected in at least one but not all valid configurations. "
			+ sep
			+ "X NEVER Y   := If X is selected Y cannot be selected in any valid configuration.";

	private ISelection selection;

	public void setActivePart(IAction action, IWorkbenchPart targetPart) {
	}

	public void run(IAction action) {
		FeatureModel fm = null;
		Node rootNode = null;

		if (!(selection instanceof IStructuredSelection))
			return;

		Iterator<?> it = ((IStructuredSelection) selection).iterator();
		Object element = it.next();
		IFile inputFile = getInputFile(element);
		if (inputFile == null)
			return;

		fm = readModel(inputFile);
		rootNode = createRootNode(fm);
		final Node node = rootNode;
		final FeatureModel mod = fm;
		Job job = new Job("Calculating Feature Dependencies") {
			protected IStatus run(IProgressMonitor monitor) {
				final String text = createText(mod.getFeatureNames(), node);
				// UI access
				final StringBuffer path = new StringBuffer();
				Display.getDefault().syncExec(new Runnable() {

					@Override
					public void run() {
						path.append(openFileDialog());
					}

				});
				saveFile(LEGEND_TEXT + text, path.toString());
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
	 * creates a String containing all information about feature dependencies
	 * 
	 * @param featureNames
	 *            the names of all features in the featuremodel
	 * @param rootNode
	 *            the Node representing the Model
	 */
	private String createText(Set<String> featureNames, Node rootNode) {
		StringBuffer textBuf = new StringBuffer();
		for (String s : featureNames) {

			try {

				textBuf.append(sep
						+ createFeatureText(rootNode, s, featureNames));
			} catch (TimeoutException e) {
				FMUIPlugin.getDefault().logError(e);
			}

		}
		return textBuf.toString();
	}

	/**
	 * creates the Node representation of the featureModel
	 * 
	 * @param fm
	 *            featureModel
	 * @return Node representing the featureModel
	 */
	private Node createRootNode(FeatureModel fm) {
		Node rootNode = NodeCreator.createNodes(fm, true);
		rootNode = rootNode.toCNF();
		return rootNode;
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
		XmlFeatureModelReader fmReader = new XmlFeatureModelReader(fm,inputFile.getProject());

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

	/**
	 * creates a String that contains feature dependency information for a
	 * certain feature
	 * 
	 * @param node
	 *            the node representing the featureModel
	 * @param name
	 *            of the feature
	 * @return String
	 * @throws TimeoutException
	 */
	private String createFeatureText(Node node, String currentFeature,
			Set<String> featureNames) throws TimeoutException {
		TreeSet<String> featureString = new TreeSet<String>();
		Node nodeSel = new And(node, new Literal(currentFeature));

		for (String s : featureNames) {
			if (!s.equals(currentFeature)) {
				if (nodeImpliesFeature(nodeSel, s, true) == true) {
					featureString.add(sep+currentFeature + " ALWAYS " + s);
				} else if (nodeImpliesFeature(nodeSel, s, false) == true) {
					featureString.add(sep+currentFeature + " NEVER " + s);
				} else {
					featureString.add(sep+currentFeature + " MAYBE " + s);
				}
			}
		}
		StringBuffer b = new StringBuffer();

		for (String s : featureString) {
			b.append(s + s);
		}
		return b.toString();
	}

	/**
	 * @param node
	 * @param s
	 * @param positive
	 *            if false, the feature is negated
	 * @return true if the given feature is selected in every valid
	 *         configuration for the featureModel represented by node
	 * @throws TimeoutException
	 */
	private boolean nodeImpliesFeature(Node node, String featureName,
			boolean positive) throws TimeoutException {
		Node nodeNeg = null;
		if (positive) {
			nodeNeg = new Not((new Implies(node, new Literal(featureName))));
		} else {
			nodeNeg = new Not((new Implies(node, new Not(featureName))));
		}
		SatSolver solver = new SatSolver(nodeNeg, 2500);
		return !solver.isSatisfiable();

	}

	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

}
