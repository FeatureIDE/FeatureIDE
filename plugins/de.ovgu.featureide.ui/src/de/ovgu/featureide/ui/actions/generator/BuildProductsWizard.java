/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.actions.generator;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * A Wizard to create T-Wise configurations with SPLCATool. 
 * 
 * @author Jens Meinicke
 */
public class BuildProductsWizard extends Wizard implements INewWizard, IConfigurationBuilderBasics {

	private IFeatureProject featureProject;
	private BuildProductsPage page;
	private boolean toggleState;

	public BuildProductsWizard(IFeatureProject featureProject, boolean toggleState) {
		this.featureProject = featureProject;
		this.toggleState = toggleState;
	}

	public boolean performFinish() {
		toggleState = page.getToggleState();
		setTWise(page.getAlgorithm(), page.getT());
		setGenerate(page.getBuildTypeText(page.getGeneration()));
		setOrder(page.getSelectedOrder());
		setTest(page.getTest());
		new ConfigurationBuilder(featureProject, page.getGeneration(),
				toggleState, page.getAlgorithm(), page.getT(), page.getOrder(), page.getTest());
		
		return true;
	}

	@Override
	public void addPages() {
		setWindowTitle("Build Products");
		page = new BuildProductsPage(featureProject.getProjectName(), featureProject, getGenerate(), toggleState, getAlgorithm(), getT(), getOrder(), getTest());
		addPage(page);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {
	}
	
	public boolean getToggleState() {
		return toggleState;
	}
	
	private String getAlgorithm() {
		String tWise = getTWise();
		if (tWise == null) {
			return ICPL;
		}
		String algorithm = tWise.split("[|]")[0];
		if (!(algorithm.equals(ICPL) ||
			  algorithm.equals(CASA) ||
			  algorithm.equals(CHVATAL))) {
			// return the default algorithm if the algorithm was saved wrong
			return ICPL;
		}
		return algorithm;
	}
	
	private int getT() {
		String tWise = getTWise();
		if (tWise == null) {
			return 2;
		}
		return Integer.parseInt(tWise.split("[|]")[1]);
	}
	
	/**
	 * Gets the toggle state from persistent properties
	 */
	protected static String getTWise() {
		try {
			return ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(T_WISE);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	/**
	 * Saves the toggle state of the dialog at persistent properties
	 */
	protected static void setTWise(String algorithm, int t) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(T_WISE, algorithm + "|" + t);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	private static String getGenerate() {
		try {
			final String generate = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(GENERATE);
			if (generate == null) {
				return ALL_VALID_CONFIGURATIONS;
			}
			return generate;
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return ALL_VALID_CONFIGURATIONS;
	}
	
	private static void setGenerate(String generate) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(GENERATE, generate);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	private static String getOrder() {
		try {
			final String generate = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(ORDER);
			if (generate == null) {
				return DEFAULT;
			}
			return generate;
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return DEFAULT;
	}
	
	private static void setOrder(String order) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(ORDER, order);
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
	
	private static boolean getTest() {
		try {
			final String test = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(TEST);
			if ("true".equals(test)) {
				return true;
			}
			if ("false".equals(test)) {
				return false;
			}
			return true;
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}
	
	private static void setTest(boolean test) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(TEST, test + "");
		} catch (CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
}
