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
package de.ovgu.featureide.examples.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.FEATUREIDE_EXAMPLE_IMPORT;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.examples.ExamplePlugin;

/**
 * Class implements the Wizard for the examples.
 * 
 * @author Christian Becker
 */
public class ExampleNewWizard extends Wizard implements INewWizard {

	public static final String ID = ExamplePlugin.PLUGIN_ID;//"de.ovgu.featureide.examples";

	private ExampleNewWizardPage mainPage = null;

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
		mainPage = new ExampleNewWizardPage();
		addPage(mainPage);
	}

	public void init(IWorkbench workbench, IStructuredSelection currentSelection) {
		setWindowTitle(FEATUREIDE_EXAMPLE_IMPORT);
	}

	public boolean performCancel() {
		return true;
	}

	public boolean performFinish() {
		return mainPage.createProjects();
	}

}
