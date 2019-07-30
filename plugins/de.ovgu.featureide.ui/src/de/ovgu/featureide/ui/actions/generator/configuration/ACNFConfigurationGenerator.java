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

import java.util.List;
import java.util.concurrent.LinkedBlockingQueue;

import de.ovgu.featureide.fm.core.analysis.cnf.CNF;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.analysis.cnf.formula.NoAbstractCNFCreator;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.IConfigurationGenerator;
import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.Selection;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.actions.generator.ConfigurationBuilder;

/**
 * Abstract class to generate configurations.
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public abstract class ACNFConfigurationGenerator extends AConfigurationGenerator {

	private class Consumer implements Runnable {

		private final IConfigurationGenerator gen;
		private final Configuration configuration = new Configuration(snapshot);
		private boolean run = true;

		public Consumer(IConfigurationGenerator gen) {
			this.gen = gen;
		}

		@Override
		public void run() {
			final LinkedBlockingQueue<LiteralSet> resultQueue = gen.getResultQueue();
			while (run) {
				try {
					generateConfiguration(resultQueue.take());
				} catch (final InterruptedException e) {
					break;
				}
			}
			setConfigurationNumber(gen.getResult().getResult().size());
			for (final LiteralSet c : resultQueue) {
				generateConfiguration(c);
			}
		}

		public void stop() {
			run = false;
		}

		private void generateConfiguration(LiteralSet solution) {
			configuration.resetValues();
			for (final int selection : solution.getLiterals()) {
				final String name = cnf.getVariables().getName(selection);
				configuration.setManual(name, selection > 0 ? Selection.SELECTED : Selection.UNSELECTED);
			}
			addConfiguration(configuration);
		}

	}

	protected final CNF cnf;

	public ACNFConfigurationGenerator(ConfigurationBuilder builder, FeatureModelFormula formula) {
		super(builder, formula);
		cnf = snapshot.getElement(new NoAbstractCNFCreator());
	}

	@Override
	protected void cancelGenerationJobs() {
		builder.cancelGenerationJobs();
	}

	@Override
	public List<LiteralSet> execute(IMonitor<List<LiteralSet>> monitor) throws Exception {
		final IConfigurationGenerator gen = getGenerator(cnf, (int) builder.configurationNumber);
		final Consumer consumer = new Consumer(gen);
		final Thread thread = new Thread(consumer);
		thread.start();
		try {
			LongRunningWrapper.runMethod(gen, monitor.subTask(1));
		} catch (final Exception e) {
			handleException(e);
			throw e;
		}
		consumer.stop();
		thread.interrupt();
		return null;
	}

	protected void handleException(Exception e) {}

	protected abstract IConfigurationGenerator getGenerator(CNF cnf, int numberOfConfigurations);

}
