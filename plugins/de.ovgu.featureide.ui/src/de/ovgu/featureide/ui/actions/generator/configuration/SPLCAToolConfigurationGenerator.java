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
package de.ovgu.featureide.ui.actions.generator.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.CASA;

import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeoutException;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.ui.internal.util.BundleUtility;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.WorkMonitor;
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
	public Void execute(WorkMonitor monitor) throws Exception {
		runSPLCATool();
		return null;
	}

	@SuppressWarnings("deprecation")
	private void runSPLCATool() {
		CoveringArray ca = null;
		try {
			if (algorithm.equals(CASA.substring(0, CASA.indexOf(" ")))) {
				URL url = BundleUtility.find(UIPlugin.getDefault().getBundle(), "lib/cover.exe");
				try {
					url = FileLocator.toFileURL(url);
				} catch (IOException e) {
					UIPlugin.getDefault().logError(e);
				}
				Path path = new Path(url.getFile());
				CoveringArrayCASA.CASA_PATH = path.toOSString();
			}

			ca = new GUIDSL(new de.ovgu.featureide.fm.core.FeatureModel(featureModel)).getSXFM().getCNF().getCoveringArrayGenerator(algorithm, t);
			if (ca == null) {
				return;
			}
			ca.generate();
		} catch (FeatureModelException e) {
			UIPlugin.getDefault().logError(e);
		} catch (TimeoutException e) {
			UIPlugin.getDefault().logError(e);
		} catch (CoveringArrayGenerationException e) {
			UIPlugin.getDefault().logError(e);
		}

		List<List<String>> solutions = Collections.emptyList();
		try{
			solutions = removeDuplicates(ca);
		}catch(Exception e){
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
	 * The result of the generator can:<br>
	 * a) contain duplicate solutions<br>
	 * b) duplicate solutions that differ only by the selection of abstract
	 * features
	 * 
	 * @return Duplicate free solutions
	 */
	private List<List<String>> removeDuplicates(final CoveringArray ca) {
		final List<List<Integer>> solutions = ca.getSolutionsAsList();
		final List<List<String>> duplicateFreeSolutions = new LinkedList<List<String>>();
		for (final List<Integer> solution : solutions) {
			final List<String> convertedSolution = new LinkedList<String>();
			for (final Integer i : solution) {
				if (i > 0) {
					String id = ca.getId(i);
					final IFeature feature = featureModel.getFeature(id);
					if (feature != null && feature.getStructure().isConcrete()) {
						convertedSolution.add(feature.getName());
					}
				}
			}
			if (!duplicateFreeSolutions.contains(convertedSolution)) {
				duplicateFreeSolutions.add(convertedSolution);
			}
		}
		if (solutions.size() - duplicateFreeSolutions.size() > 0) {
			UIPlugin.getDefault().logInfo((solutions.size() - duplicateFreeSolutions.size()) + " duplicate solutions skipped!");
		}
		return duplicateFreeSolutions;
	}

}
