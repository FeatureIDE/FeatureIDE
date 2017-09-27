/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.ALL_VALID_CONFIGURATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_PRODUCTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CASA;
import static de.ovgu.featureide.fm.core.localization.StringTable.CHVATAL;
import static de.ovgu.featureide.fm.core.localization.StringTable.DEFAULT;
import static de.ovgu.featureide.fm.core.localization.StringTable.ICPL;
import static de.ovgu.featureide.fm.core.localization.StringTable.INCLING;

import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.ui.INewWizard;
import org.eclipse.ui.IWorkbench;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FMCorePlugin;

/**
 * A Wizard to create configurations with the {@link ConfigurationBuilder}.
 *
 * @author Jens Meinicke
 */
public class BuildProductsWizard extends Wizard implements INewWizard, IConfigurationBuilderBasics {

	private final IFeatureProject featureProject;
	private BuildProductsPage page;
	private boolean toggleState;

	public BuildProductsWizard(IFeatureProject featureProject, boolean toggleState) {
		this.featureProject = featureProject;
		this.toggleState = toggleState;
	}

	@Override
	public boolean performFinish() {
		toggleState = page.getToggleState();
		setTWise(page.getAlgorithm(), page.getT());
		setTOrder(page.getTInteraction());
		setGenerate(page.getBuildTypeText(page.getGeneration()));
		setOrder(page.getSelectedOrder());
		setTest(page.getTest());
		setMax(page.getMax());
		new ConfigurationBuilder(featureProject, page.getGeneration(), toggleState, page.getAlgorithm(), page.getT(), page.getOrder(), page.getTest(),
				page.getMax(), page.getTInteraction());

		return true;
	}

	@Override
	public void addPages() {
		setWindowTitle(BUILD_PRODUCTS);
		page = new BuildProductsPage(featureProject.getProjectName(), featureProject, getGenerate(), toggleState, getAlgorithm(), getT(), getT_Interaction(),
				getOrder(), getTest(), getMax());
		addPage(page);
	}

	@Override
	public void init(IWorkbench workbench, IStructuredSelection selection) {}

	public boolean getToggleState() {
		return toggleState;
	}

	private String getAlgorithm() {
		final String tWise = getTWise();
		if (tWise == null) {
			return ICPL;
		}
		final String algorithm = tWise.split("[|]")[0];
		if (!(algorithm.equals(ICPL) || algorithm.equals(CASA) || algorithm.equals(INCLING) || algorithm.equals(CHVATAL))) {
			// return the default algorithm if the algorithm was saved wrong
			return ICPL;
		}
		return algorithm;
	}

	private int getT() {
		final String tWise = getTWise();
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
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return null;
	}

	/**
	 * Gets the toggle state from persistent properties
	 */
	protected static int getT_Interaction() {
		try {
			final String generate = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(T_INTERACTION);
			if (generate == null) {
				return 2;
			}
			return Integer.parseInt(generate);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return 2;
	}

	/**
	 * Saves the toggle state of the dialog at persistent properties
	 */
	protected static void setTWise(String algorithm, int t) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(T_WISE, algorithm + "|" + t);
		} catch (final CoreException e) {
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
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return ALL_VALID_CONFIGURATIONS;
	}

	private static void setGenerate(String generate) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(GENERATE, generate);
		} catch (final CoreException e) {
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
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return DEFAULT;
	}

	private static void setOrder(String order) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(ORDER, order);
		} catch (final CoreException e) {
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
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return false;
	}

	private static void setTest(boolean test) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(TEST, test + "");
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private String getMax() {
		String returnValue = "";
		try {
			returnValue = ResourcesPlugin.getWorkspace().getRoot().getPersistentProperty(MAX);
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
		return returnValue != null ? returnValue : "";
	}

	private void setMax(int max) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(MAX, max + "");
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}

	private void setTOrder(int t) {
		try {
			ResourcesPlugin.getWorkspace().getRoot().setPersistentProperty(T_INTERACTION, t + "");
		} catch (final CoreException e) {
			FMCorePlugin.getDefault().logError(e);
		}
	}
}
