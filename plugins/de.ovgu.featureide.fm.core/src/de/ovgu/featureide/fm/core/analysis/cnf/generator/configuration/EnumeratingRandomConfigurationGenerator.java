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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public class EnumeratingRandomConfigurationGenerator extends ARandomConfigurationGenerator {

	public EnumeratingRandomConfigurationGenerator(CNF cnf, int maxNumber) {
		super(cnf, maxNumber);
	}

	@Override
	protected void generate(IMonitor monitor) throws Exception {
		monitor.setRemainingWork(maxSampleSize);

		final AllConfigurationGenerator gen = new AllConfigurationGenerator(solver);
		final List<LiteralSet> allConfigurations = new ArrayList<>(LongRunningWrapper.runMethod(gen));
		if (!allowDuplicates) {
			Collections.shuffle(allConfigurations, random);
		}

		for (int i = 0; i < maxSampleSize; i++) {
			if (allowDuplicates) {
				addResult(allConfigurations.get(random.nextInt(allConfigurations.size())));
			} else {
				if (i >= allConfigurations.size()) {
					break;
				} else {
					addResult(allConfigurations.get(i));
				}
			}
			monitor.step();
		}
	}

}
