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
package de.ovgu.featureide.ui.statistics.ui.helper;

import static de.ovgu.featureide.fm.core.localization.StringTable.REFRESH_STATISTICS_VIEW;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.IJobChangeListener;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.fm.core.job.IJob;
import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent.StatisticTreeJob;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.ui.helper.jobs.TreeJob;

/**
 * Listener for {@link TreeJob}s. Uses Singleton-Pattern.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class JobDoneListener implements IJobChangeListener {

	protected static JobDoneListener instance = new JobDoneListener();
	private final List<IJob<?>> runningJobs = new LinkedList<>();
	protected List<TreeViewer> views = new LinkedList<TreeViewer>();

	public void checkViews() {
		synchronized (views) {
			for (int i = 0; i < views.size();) {
				final TreeViewer view = views.get(i);
				if ((view == null) || (view.getControl() == null) || view.getControl().isDisposed()) {
					views.remove(view);
				} else {
					i++;
				}
			}
		}
	}

	public void init(final TreeViewer view) {
		views.add(view);
	}

	public static JobDoneListener getInstance() {
		return instance;
	}

	/**
	 * Private constructor for singleton-pattern.
	 */
	private JobDoneListener() {}

	@Override
	public void aboutToRun(IJobChangeEvent event) {}

	@Override
	public void awake(IJobChangeEvent event) {}

	/**
	 * Reverses the actions of {@link JobDoneListener#scheduled(IJobChangeEvent)}
	 */
	@Override
	public void done(final IJobChangeEvent event) {
		if ((event.getResult() == Status.OK_STATUS) || (event.getResult() == Status.CANCEL_STATUS)) {
			final UIJob refreshJob = new UIJob(REFRESH_STATISTICS_VIEW) {

				@Override
				public IStatus runInUIThread(IProgressMonitor monitor) {
					final Job job = event.getJob();
					if (job instanceof LongRunningJob) {
						final LongRunningJob<?> treeJob = (LongRunningJob<?>) job;
						final LongRunningMethod<?> method = treeJob.getMethod();
						final boolean expand = (method instanceof StatisticTreeJob) && ((StatisticTreeJob) method).isExpand();
						runningJobs.remove(treeJob);
						final Parent calc = ((TreeJob) method).getCalculated();
						calc.startCalculating(false);
						checkViews();
						synchronized (views) {
							for (final TreeViewer view : views) {
								view.refresh(calc);
								if (expand) {
									view.expandToLevel(calc, 1);
								}
							}
						}
					}
					return Status.OK_STATUS;
				}
			};
			refreshJob.setPriority(Job.INTERACTIVE);
			refreshJob.schedule();
		}
	}

	@Override
	public void running(IJobChangeEvent event) {}

	/**
	 * Adds the scheduled job to the list of running jobs and gives the user optical feedback that the requested node is being calculated.
	 */
	@Override
	public void scheduled(final IJobChangeEvent event) {
		final UIJob refreshJob = new UIJob(REFRESH_STATISTICS_VIEW) {

			@Override
			public IStatus runInUIThread(IProgressMonitor monitor) {
				final Job job = event.getJob();
				if (job instanceof LongRunningJob) {
					final LongRunningJob<?> treeJob = (LongRunningJob<?>) job;
					runningJobs.add(treeJob);
					final Parent calc = ((TreeJob) treeJob.getMethod()).getCalculated();
					calc.startCalculating(true);
					checkViews();
					synchronized (views) {
						for (final TreeViewer view : views) {
							view.refresh(calc);
						}
					}
				}
				return Status.OK_STATUS;
			}
		};
		refreshJob.setPriority(Job.INTERACTIVE);
		refreshJob.schedule();
	}

	@Override
	public void sleeping(IJobChangeEvent event) {}

	public void cancelAllRunningTreeJobs() {
		for (final IJob<?> job : runningJobs) {
			job.cancel();
		}
	}
}
