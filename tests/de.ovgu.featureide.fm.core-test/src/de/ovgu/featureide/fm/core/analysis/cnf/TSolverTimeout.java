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
package de.ovgu.featureide.fm.core.analysis.cnf;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import de.ovgu.featureide.Commons;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.ConfigurationPropagator;
import de.ovgu.featureide.fm.core.configuration.IConfigurationPropagator;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;

/**
 * Tests the timeout for the solver to prevent wrong timeouts.
 *
 * @author Joshua Sprey
 */
public class TSolverTimeout {

	@Test
	public void testSolverTimeout() {
		final IFeatureModel fm = Commons.loadBenchmarkFeatureModelFromFile("berkeley_db_model.xml");
		final FeatureModelFormula formula = new FeatureModelFormula(fm);
		final IConfigurationPropagator propagator = new ConfigurationPropagator(formula, new Configuration(formula));

		// Set timeout to 10 ms, expecting timeout
		final LongRunningMethod<Long> analysis = propagator.number(10);
		long time = System.currentTimeMillis();
		try {
			analysis.execute(null);
		} catch (final Exception e) {
			e.printStackTrace();
		}
		time = System.currentTimeMillis() - time;
		// Ensures that the solver did not mistake the 10 ms for 10 s
		assertTrue(time < 10000);
	}

}
