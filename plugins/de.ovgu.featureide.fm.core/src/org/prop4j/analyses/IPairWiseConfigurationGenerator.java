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
package org.prop4j.analyses;

import java.util.List;
import java.util.concurrent.BlockingQueue;

import org.sat4j.specs.IConstr;

import de.ovgu.featureide.fm.core.job.LongRunningMethod;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public interface IPairWiseConfigurationGenerator extends LongRunningMethod<List<List<String>>> {

	public static class Configuration {

		private static final double minBackJumpingDelta = 0.0;

		private IConstr blockingClauseConstraint = null;

		private int deltaCoverage;
		private final int[] model;
		private int totalCoverage;

		public long time = 0;

		public Configuration(int[] model, int deltaCoverage, int totalCoverage) {
			this.model = model;
			this.deltaCoverage = deltaCoverage;
			this.totalCoverage = totalCoverage;
		}

		public IConstr getBlockingClauseConstraint() {
			return blockingClauseConstraint;
		}

		public int getDeltaCoverage() {
			return deltaCoverage;
		}

		public int[] getModel() {
			return model;
		}

		public int getTotalCoverage() {
			return totalCoverage;
		}

		public boolean isBetterThan(Configuration o) {
			return (0 > (o.deltaCoverage - (deltaCoverage * (1 - minBackJumpingDelta))));
		}

		public void setBlockingClauseConstraint(IConstr blockingClauseConstraint) {
			this.blockingClauseConstraint = blockingClauseConstraint;
		}

		public void setDeltaCoverage(int deltaCoverage) {
			this.deltaCoverage = deltaCoverage;
		}

		public void setTotalCoverage(int totalCoverage) {
			this.totalCoverage = totalCoverage;
		}
	}

	public static final boolean VERBOSE = false;

	List<List<String>> getConfigurations();

	List<String> getNextConfiguration();

	int getFixedPartCount();

	BlockingQueue<Configuration> getQ();

}
