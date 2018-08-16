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
package de.ovgu.featureide.fm.core.job;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;

import de.ovgu.featureide.fm.core.Logger;
import de.ovgu.featureide.fm.core.PluginID;
import de.ovgu.featureide.fm.core.functional.Functional.IConsumer;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor.MethodCancelException;
import de.ovgu.featureide.fm.core.job.monitor.ProgressMonitor;
import de.ovgu.featureide.fm.core.job.util.JobFinishListener;

/**
 * Abstract eclipse job with support for {@link JobFinishListener}.
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke (Feature Interface)
 */
public abstract class AbstractJob<T> extends Job implements IJob<T> {

	private class JobFL extends JobChangeAdapter {

		@SuppressWarnings("rawtypes")
		private final JobFinishListener listener;

		public JobFL(@SuppressWarnings("rawtypes") JobFinishListener listener) {
			this.listener = listener;
		}

		@SuppressWarnings("unchecked")
		@Override
		public void done(IJobChangeEvent event) {
			listener.jobFinished(AbstractJob.this);
		}

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (this == obj) {
				return true;
			}
			if ((obj == null) || (getClass() != obj.getClass())) {
				return false;
			}
			return listener.equals(((JobFL) obj).listener);
		}

		@Override
		public int hashCode() {
			return listener.hashCode();
		}
	}

	private IConsumer<Object> intermediateFunction;

	protected T methodResult = null;

	private JobStatus status = JobStatus.NOT_STARTED;

	protected AbstractJob(String name, int priority) {
		super(name);
		setPriority(priority);
	}

	@SuppressWarnings("rawtypes")
	@Override
	public final void addJobFinishedListener(final JobFinishListener listener) {
		addJobChangeListener(new JobFL(listener));
	}

	@Override
	public T getResults() {
		return methodResult;
	}

	@Override
	public final JobStatus getStatus() {
		return status;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public final void removeJobFinishedListener(JobFinishListener listener) {
		removeJobChangeListener(new JobFL(listener));
	}

	@Override
	public final IStatus run(IProgressMonitor monitor) {
		status = JobStatus.RUNNING;

		// run job and catch possible runtime exceptions
		final ProgressMonitor workMonitor = new ProgressMonitor(getName(), monitor);
		workMonitor.setIntermediateFunction(intermediateFunction);
		try {
			methodResult = work(workMonitor);
			status = JobStatus.OK;
		} catch (final MethodCancelException e) {
			status = JobStatus.FAILED;
			throw new OperationCanceledException();
		} catch (final Exception e) {
			status = JobStatus.FAILED;
			Logger.logError(e);
			return new Status(IStatus.ERROR, PluginID.PLUGIN_ID, "FAILED", e);
		} finally {
			finalWork();
			workMonitor.done();
		}

		return Status.OK_STATUS;
	}

	@Override
	public final void setIntermediateFunction(IConsumer<Object> intermediateFunction) {
		this.intermediateFunction = intermediateFunction;
	}

	@Override
	public Class<?> getImplementationClass() {
		return getClass();
	}

	/**
	 * This method is called after {@link #work()} is finished regardless whether it succeeded or not. The default method is empty.
	 *
	 * @param success {@code true} if the execution of {@link #work()} was complete and successful, {@code false} otherwise
	 */
	protected void finalWork() {}

	/**
	 * In this method all the work of the job is done.</br> Use the {@link #workMonitor} field for progress monitoring and calling intermediate functions.</br>
	 * </br> Implementing jobs should continuously call {@link IMonitor#checkCancel()}.
	 *
	 * @return {@code true} if no error occurred during the process
	 * @throws Exception any exception (will be catched by the parent class)
	 */
	protected abstract T work(IMonitor workMonitor) throws Exception;

}
