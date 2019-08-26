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
package de.ovgu.featureide.ui.actions.generator.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.OK;

import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.IConfigurationGenerator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.SPLCAToolConfigurationGenerator;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Generates T-wise configurations using SPLATool.
 *
 * @author Sebastian Krieter
 */
public class CASAConfigurationGenerator extends ACNFConfigurationGenerator {

	private final int t;

	public CASAConfigurationGenerator(ConfigurationBuilder builder, FeatureModelFormula formula, int t) {
		super(builder, formula);
		this.t = t;
	}

	@Override
	protected IConfigurationGenerator getGenerator(CNF cnf, int numberOfConfigurations) {
		return new SPLCAToolConfigurationGenerator(cnf, "CASA", t, numberOfConfigurations);
	}

	@Override
	protected void handleException(final Exception e) {
		final Display display = Display.getDefault();
		display.syncExec(new Runnable() {
			@Override
			public void run() {
				final String errorMessage = "CASA experienced an error during its execution.\nMessage: " + e.getMessage()
					+ "\nMaybe some dependent libraries are missing (e.g., libgcc_s_dw2-1.dll or libstdc++-6.dll)";
				new MessageDialog(display.getActiveShell(), "External Execution Error", GUIDefaults.FEATURE_SYMBOL, errorMessage, MessageDialog.ERROR,
						new String[] { OK }, 0).open();
			}
		});
	}

}
