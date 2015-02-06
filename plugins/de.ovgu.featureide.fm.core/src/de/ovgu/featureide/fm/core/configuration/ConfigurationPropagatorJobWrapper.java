/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.fm.core.job.IStoppableJob;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationPropagatorJobWrapper {
	public static interface IConfigJob<T> extends IStoppableJob {
		public static final int 
			ID_LOAD = 0,
			ID_SOLUTIONS = 1,
			ID_ISVALID = 2,
			ID_CANBEVALID = 3,
			ID_VALIDCONFIG = 4,
			ID_NUMBER = 5,
			ID_UPDATE = 6;
		
		public T getResults();
		
		public int getID();
	}
	
	private static abstract class ConfigJob<T> extends AStoppableJob implements IConfigJob<T> {
		protected T result = null;
		protected final int id;
		
		public ConfigJob(int id) {
			super(getName(id));
			this.id = id;
		}
		
		private static String getName(int id) {
			switch (id) {
			case ID_LOAD: return "Loading CNF";
			case ID_SOLUTIONS: return "Calculating Configuration Solutions";
			case ID_ISVALID: return "Checking Configuration Validity";
			case ID_CANBEVALID: return "Checking Configuration Validity";
			case ID_VALIDCONFIG: return "Calculating Configuration Coloring";
			case ID_NUMBER: return "Calculating Number of Valid Configurations";
			case ID_UPDATE: return "Updating Configuration";
			default: return "Configuration Job";
			}
		}

		public T getResults() {
			return result;
		}

		@Override
		public int getID() {
			return id;
		}
	}

	private final ConfigurationPropagator propagator;
	
	public ConfigurationPropagatorJobWrapper(ConfigurationPropagator propagator) {
		this.propagator = propagator;
	}
	
	public IConfigJob<?> load() {
		return new ConfigJob<Object>(ConfigJob.ID_LOAD) {
			@Override
			protected boolean work() throws Exception {
				propagator.load(workMonitor);
				return true;
			}
		};
	}

	public IConfigJob<LinkedList<List<String>>> getSolutions(final int max) {
		return new ConfigJob<LinkedList<List<String>>>(ConfigJob.ID_SOLUTIONS) {
			@Override
			protected boolean work() throws Exception {
				result = propagator.getSolutions(max, workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<Boolean> isValid() {
		return new ConfigJob<Boolean>(ConfigJob.ID_ISVALID) {
			@Override
			protected boolean work() throws Exception {
				result = propagator.isValid(workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<Boolean> canBeValid() {
		return new ConfigJob<Boolean>(ConfigJob.ID_CANBEVALID) {
			@Override
			protected boolean work() throws Exception {
				result = propagator.canBeValid(workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<?> leadToValidConfiguration(final List<SelectableFeature> featureList) {
		return new ConfigJob<Object>(ConfigJob.ID_VALIDCONFIG) {
			@Override
			protected boolean work() throws Exception {
				propagator.leadToValidConfiguration(featureList, workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<?> leadToValidConfiguration(final List<SelectableFeature> featureList, final int mode) {
		return new ConfigJob<Object>(ConfigJob.ID_VALIDCONFIG) {
			@Override
			protected boolean work() throws Exception {
				propagator.leadToValidConfiguration(featureList, mode, workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<Long> number(final long timeout) {
		return new ConfigJob<Long>(ConfigJob.ID_NUMBER) {
			@Override
			protected boolean work() throws Exception {
				result = propagator.number(timeout, workMonitor);
				return true;
			}
		};
	}
	
	public IConfigJob<?> update(final boolean redundantManual, final String startFeature) {
		return new ConfigJob<Object>(ConfigJob.ID_UPDATE) {
			@Override
			protected boolean work() throws Exception {
				propagator.update(redundantManual, startFeature, workMonitor);
				return true;
			}
		};
	}
}
