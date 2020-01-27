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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import static de.ovgu.featureide.fm.core.localization.StringTable.CASA;

import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.concurrent.TimeoutException;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.IVariables;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.Variables;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.DefaultFeatureModelFactory;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormat;
import de.ovgu.featureide.fm.core.io.dimacs.DIMACSFormatCNF;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import no.sintef.ict.splcatool.CoveringArray;
import no.sintef.ict.splcatool.CoveringArrayCASA;
import no.sintef.ict.splcatool.CoveringArrayGenerationException;
import no.sintef.ict.splcatool.GUIDSL;
import splar.core.fm.FeatureModelException;

/**
 * Generates T-wise configurations using SPLATool.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class SPLCAToolConfigurationGenerator extends de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.AConfigurationGenerator
		implements ITWiseConfigurationGenerator {

	private final IFeatureModel featureModel;
	private final Variables renamedVariables;
	private final String algorithm;
	private final int t;

	public SPLCAToolConfigurationGenerator(CNF cnf, String algorithm, int t, int maxSampleSize) {
		super(cnf, maxSampleSize);
		featureModel = DefaultFeatureModelFactory.getInstance().create();

		renamedVariables = (Variables) cnf.getVariables().clone();
		int index = 1;
		for (final String originalName : cnf.getVariables().getNames()) {
			renamedVariables.renameVariable(originalName, "F" + index++);
		}
		final String dimacsSource = new DIMACSFormatCNF().write(new CNF(renamedVariables, cnf.getClauses()));
		new DIMACSFormat().read(featureModel, dimacsSource);
		this.algorithm = algorithm;
		this.t = t;
	}

	@Override
	protected void generate(IMonitor<List<LiteralSet>> monitor) throws Exception {
		CoveringArray ca = null;
		final boolean casa = algorithm.equals(CASA.substring(0, CASA.indexOf(" ")));
		try {
			if (casa) {
				final String string = FileSystem.getLib(Paths.get("lib/cover.exe")).toString();
				CoveringArrayCASA.CASA_PATH = string;
			}

			ca = new GUIDSL(featureModel).getSXFM().getCNF().getCoveringArrayGenerator(algorithm, t);
			if (ca == null) {
				return;
			}
			ca.generate();
		} catch (FeatureModelException | TimeoutException | CoveringArrayGenerationException e) {
			Logger.logError(e);
			return;
		} catch (final Exception e) {
			Logger.logError(e);
			return;
		}

		List<List<String>> solutions = Collections.emptyList();
		try {
			solutions = removeDuplicates(ca);
		} catch (final Exception e) {
			Logger.logWarning("Problems occurred during the execution of " + algorithm);
		}
		final IVariables variables = solver.getSatInstance().getVariables();
		for (final List<String> solution : solutions) {
			final int[] literals = new int[variables.size()];
			for (int i = 0; i < literals.length; i++) {
				literals[i] = -(i + 1);
			}
			for (final String selection : solution) {
				final int varIndex = renamedVariables.getVariable(selection);
				final int variable = solver.getSatInstance().getInternalVariables().convertToInternal(varIndex);
				if (variable != 0) {
					literals[variable - 1] = variable;
				}
			}
			addResult(new LiteralSet(literals, LiteralSet.Order.INDEX));
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
			Logger.logInfo(difference + " duplicate solutions skipped!");
		}
		return duplicateFreeSolutionList;
	}

}
