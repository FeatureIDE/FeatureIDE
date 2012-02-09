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
package de.ovgu.featureide.examples.wizards;

import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;
import org.osgi.framework.Bundle;

import de.ovgu.featureide.examples.ExamplePlugin;


/**
 * Class implements the Wizard for the examples.
 * 
 * @author Christian Becker
 */
public class ExampleNewWizard extends Wizard implements INewWizard {

	public static final String ID = ExamplePlugin.PLUGIN_ID;//"de.ovgu.featureide.examples";
	private static final String FeatureIDE_EXAMPLE_DIR = "featureide_examples";//$NON-NLS-1$

	private ExampleNewWizardPage mainPage;
	private String samplePath = "";

	/**
	 * Constructor for SampleNewWizard.
	 */
	public ExampleNewWizard() {
		super();
		setNeedsProgressMonitor(true);
	}

	/**
	 * Adding the page to the wizard.
	 */
	public void addPages() {
		mainPage = new ExampleNewWizardPage(samplePath);
		addPage(mainPage);
	}

	/*
	 * (non-Javadoc) Method declared on IWorkbenchWizard.
	 */
	public void init(IWorkbench workbench, IStructuredSelection currentSelection) {
		setWindowTitle("FeatureIDE Example Import");

		// get the path for the examples - it can be a jar-file or folder
		// structure
		try {
			Bundle bundle = Platform.getBundle(ID);
			URL realURL = FileLocator.resolve(bundle.getEntry("/"));
			samplePath = realURL.getPath();

			// check if is jar file
			if (samplePath.startsWith("file")) {
				samplePath = samplePath.substring(5, samplePath.length() - 2);
			} else {
				// is folder
				samplePath += FeatureIDE_EXAMPLE_DIR;
			}

		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
		}
	}

	/*
	 * (non-Javadoc) Method declared on IWizard.
	 */
	public boolean performCancel() {
		mainPage.performCancel();
		return true;
	}

	/*
	 * (non-Javadoc) Method declared on IWizard.
	 */
	public boolean performFinish() {
		return mainPage.createProjects();
	}

}