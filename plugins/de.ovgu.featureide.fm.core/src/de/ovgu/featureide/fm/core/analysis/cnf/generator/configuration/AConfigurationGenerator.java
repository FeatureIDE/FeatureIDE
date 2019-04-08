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
import java.util.List;
import java.util.concurrent.LinkedBlockingQueue;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.Solution;
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Order;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.ITWiseConfigurationGenerator.Phase;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public abstract class AConfigurationGenerator extends AbstractAnalysis<List<Solution>> implements IConfigurationGenerator {

	public static Order order = Order.SORTED;
	public static Phase phase = Phase.SINGLE;

	protected final int maxSampleSize;

	private final List<Solution> resultList = new ArrayList<>();
	private final LinkedBlockingQueue<Solution> resultQueue;

	public AConfigurationGenerator(CNF cnf) {
		this(cnf, Integer.MAX_VALUE);
	}

	public AConfigurationGenerator(ISatSolver solver) {
		this(solver, Integer.MAX_VALUE);
	}

	public AConfigurationGenerator(CNF cnf, int maxSampleSize) {
		super(cnf);
		this.maxSampleSize = maxSampleSize;
		resultQueue = new LinkedBlockingQueue<>();
	}

	public AConfigurationGenerator(ISatSolver solver, int maxSampleSize) {
		super(solver);
		this.maxSampleSize = maxSampleSize;
		resultQueue = new LinkedBlockingQueue<>();
	}

	@Override
	public List<Solution> analyze(IMonitor monitor) throws Exception {
		resultList.clear();
		resultQueue.clear();

		generate(monitor);

		return resultList;
	}

	protected abstract void generate(IMonitor monitor) throws Exception;

	protected void addResult(Solution result) {
		resultList.add(result);
		try {
			resultQueue.put(result);
		} catch (final InterruptedException e) {
			Logger.logError(e);
		}
	}

	@Override
	public LinkedBlockingQueue<Solution> getResultQueue() {
		return resultQueue;
	}

}
