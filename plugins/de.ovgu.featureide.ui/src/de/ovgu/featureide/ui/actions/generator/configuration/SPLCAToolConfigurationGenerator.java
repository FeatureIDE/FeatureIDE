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
package de.ovgu.featureide.ui.actions.generator.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.CASA;
import static de.ovgu.featureide.fm.core.localization.StringTable.OK;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.TimeoutException;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.internal.util.BundleUtility;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;
import no.sintef.ict.splcatool.CoveringArray;
import no.sintef.ict.splcatool.CoveringArrayCASA;
import no.sintef.ict.splcatool.CoveringArrayGenerationException;
import no.sintef.ict.splcatool.GUIDSL;
import splar.core.fm.FeatureModelException;

/**
 * Generates T-wise configurations using SPLATool.
 *
 * @author Jens Meinicke
 */
@SuppressWarnings("restriction")
public class SPLCAToolConfigurationGenerator extends AConfigurationGenerator {

	private final String algorithm;
	private final int t;

	public SPLCAToolConfigurationGenerator(ConfigurationBuilder builder, IFeatureModel featureModel, IFeatureProject featureProject, String algorithm, int t) {
		super(builder, featureModel, featureProject);
		this.algorithm = algorithm;
		this.t = t;
	}

	@Override
	public Void execute(IMonitor monitor) throws Exception {
		runSPLCATool();
		return null;
	}

	@SuppressWarnings("deprecation")
	private void runSPLCATool() {
		CoveringArray ca = null;
		final boolean casa = algorithm.equals(CASA.substring(0, CASA.indexOf(" ")));
		try {
			if (casa) {
				URL url = BundleUtility.find(UIPlugin.getDefault().getBundle(), "lib/cover.exe");
				try {
					url = FileLocator.toFileURL(url);
				} catch (final IOException e) {
					UIPlugin.getDefault().logError(e);
				}
				final Path path = new Path(url.getFile());
				CoveringArrayCASA.CASA_PATH = path.toOSString();
			}

			ca = new GUIDSL(new de.ovgu.featureide.fm.core.FeatureModel(featureModel)).getSXFM().getCNF().getCoveringArrayGenerator(algorithm, t);
			if (ca == null) {
				return;
			}
			ca.generate();
		} catch (FeatureModelException | TimeoutException | CoveringArrayGenerationException e) {
			UIPlugin.getDefault().logError(e);
			return;
		} catch (final Exception e) {
			final Display display = Display.getDefault();
			display.syncExec(new Runnable() {

				@Override
				public void run() {
					final String errorMessage = algorithm + " experienced an error during its execution.\n"
						+ (casa ? "Maybe some dependent libraries are missing (e.g., libgcc_s_dw2-1.dll or libstdc++-6.dll)" : "Message:\n\t" + e.getMessage());
					new MessageDialog(display.getActiveShell(), "External Execution Error", GUIDefaults.FEATURE_SYMBOL, errorMessage, MessageDialog.ERROR,
							new String[] { OK }, 0).open();
				}
			});
			return;
		}

		List<List<String>> solutions = Collections.emptyList();
		try {
			solutions = removeDuplicates(ca);
		} catch (final Exception e) {
			UIPlugin.getDefault().logWarning("Problems occurred during the execution of " + algorithm);
		}
		builder.configurationNumber = solutions.size();
		for (final List<String> solution : solutions) {
			configuration.resetValues();
			for (final String selection : solution) {
				configuration.setManual(selection, Selection.SELECTED);
			}
			addConfiguration(configuration);
		}
	}

	/**
	 * The result of the generator can:<br> a) contain duplicate solutions<br> b) duplicate solutions that differ only by the selection of abstract features
	 *
	 * @return Duplicate free solutions
	 */
	private List<List<String>> removeDuplicates(final CoveringArray ca) {
		final List<List<Integer>> solutions = ca.getSolutionsAsList();
		final HashSet<List<String>> duplicateFreeSolutions = new HashSet<>();
		final List<List<String>> duplicateFreeSolutionList = new ArrayList<>();
		for (final List<Integer> solution : solutions) {
			final List<String> convertedSolution = new ArrayList<>();
			for (final Integer i : solution) {
				if (i > 0) {
					final String id = ca.getId(i);
					final IFeature feature = featureModel.getFeature(id);
					if ((feature != null) && feature.getStructure().isConcrete()) {
						convertedSolution.add(feature.getName());
					}
				}
			}
			Collections.sort(convertedSolution);
			if (duplicateFreeSolutions.add(convertedSolution)) {
				duplicateFreeSolutionList.add(convertedSolution);
			}
		}
		final int difference = solutions.size() - duplicateFreeSolutions.size();
		if (difference > 0) {
			UIPlugin.getDefault().logInfo(difference + " duplicate solutions skipped!");
		}
		return duplicateFreeSolutionList;
	}

}
