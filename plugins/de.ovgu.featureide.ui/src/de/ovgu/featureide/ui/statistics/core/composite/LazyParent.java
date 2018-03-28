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
package de.ovgu.featureide.ui.statistics.core.composite;

import static de.ovgu.featureide.fm.core.localization.StringTable.CALCULATE;

import java.util.LinkedList;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.job.IRunner;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.ui.statistics.ui.helper.JobDoneListener;
import de.ovgu.featureide.ui.statistics.ui.helper.jobs.TreeJob;

/**
 * Provides functionality for lazy calculating its children for the {@link TreeViewer}. {@link LazyParent#initChildren()} has to be overridden using the
 * LazyParent#addChild(Parent)-method to initialize.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public abstract class LazyParent extends Parent {

	public final class StatisticTreeJob extends TreeJob {

		private final boolean expand;

		private StatisticTreeJob(Parent calculated, boolean expand) {
			super(calculated);
			this.expand = expand;
		}

		public boolean isExpand() {
			return expand;
		}

		@Override
		public Boolean execute(IMonitor monitor) throws Exception {
			try {
				initChildren();
			} finally {
				setCalculating(false);
			}
			return true;
		}

		@Override
		public boolean cancel() {
			return false;
		}

	}

	protected boolean lazy = true;

	@Override
	public Parent[] getChildren() {
		return calculateChidren(true);
	}

	/**
	 * Starts a job, that calculates the children of this instance, and registers it to the listener.
	 */
	protected Parent[] calculateChidren(boolean expand) {
		if (lazy) {
			final TreeJob job = new StatisticTreeJob(this, expand);
			final IRunner<Boolean> runner = LongRunningWrapper.getRunner(job, CALCULATE + this.getClass().getName());
			if (runner instanceof LongRunningJob<?>) {
				((LongRunningJob<?>) runner).setPriority(Job.SHORT);
				final JobDoneListener listener = JobDoneListener.getInstance();
				if (listener != null) {
					((LongRunningJob<?>) runner).addJobChangeListener(listener);
				}
			}
			runner.schedule();
		}
		lazy = false;
		return super.getChildren();
	}

	/**
	 * May be overridden in order to change the priority. Should be used especially for lengthy calculations.
	 *
	 * @param job
	 */
	protected void setPriority(Job job) {
		job.setPriority(Job.SHORT);
	}

	public boolean isLazy() {
		return lazy;
	}

	public void setLazy(boolean lazy) {
		this.lazy = lazy;
	}

	@Override
	public Boolean hasChildren() {
		return lazy || super.hasChildren();
	}

	/**
	 * Must be implemented to initialize this node lazily. Therefore this method must use {@link Parent#addChild(Parent)}.
	 */
	protected abstract void initChildren();

	public LazyParent(String description, Object value) {
		super(description, value);
	}

	protected LazyParent() {
		super();
	}

	public LazyParent(String description) {
		super(description);
	}

	public void recalculate() {
		children = new LinkedList<Parent>();
		initChildren();
	}
}
