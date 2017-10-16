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
import de.ovgu.featureide.fm.core.analysis.cnf.analysis.AbstractAnalysis;
import de.ovgu.featureide.fm.core.analysis.cnf.solver.ISatSolver;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Finds certain solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public abstract class AConfigurationGenerator extends AbstractAnalysis<List<int[]>> {

	protected final int maxNumber;

	private final List<int[]> resultList = new ArrayList<>();
	private final LinkedBlockingQueue<int[]> resultQueue;

	public AConfigurationGenerator(CNF cnf) {
		this(cnf, Integer.MAX_VALUE, false);
	}

	public AConfigurationGenerator(ISatSolver solver) {
		this(solver, Integer.MAX_VALUE, false);
	}

	public AConfigurationGenerator(CNF cnf, int maxNumber) {
		this(cnf, maxNumber, false);
	}

	public AConfigurationGenerator(CNF cnf, int maxNumber, boolean incremental) {
		super(cnf);
		this.maxNumber = maxNumber;
		resultQueue = incremental ? new LinkedBlockingQueue<int[]>() : null;
	}

	public AConfigurationGenerator(ISatSolver solver, int maxNumber, boolean incremental) {
		super(solver);
		this.maxNumber = maxNumber;
		resultQueue = incremental ? new LinkedBlockingQueue<int[]>() : null;
	}

	@Override
	public List<int[]> analyze(IMonitor monitor) throws Exception {
		resultList.clear();
		if (resultQueue != null) {
			resultQueue.clear();
		}

		generate(monitor);

		return resultList;
	}

	protected abstract void generate(IMonitor monitor) throws Exception;

	protected void addResult(int[] result) {
		resultList.add(result);
		if (resultQueue != null) {
			try {
				resultQueue.put(result);
			} catch (final InterruptedException e) {
				Logger.logError(e);
			}
		}
	}

	public LinkedBlockingQueue<int[]> getResultQueue() {
		return resultQueue;
	}

}
