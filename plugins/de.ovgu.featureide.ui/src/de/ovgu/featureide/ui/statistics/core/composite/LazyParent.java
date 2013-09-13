package de.ovgu.featureide.ui.statistics.core.composite;

import java.util.LinkedList;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.ui.statistics.ui.helper.JobDoneListener;
import de.ovgu.featureide.ui.statistics.ui.helper.jobs.TreeJob;

/**
 * Provides functionality for lazy calculating its children for the
 * {@link TreeViewer}. {@link LazyParent#initChildren()} has to be overridden
 * using the LazyParent#addChild(Parent)-method to initialize.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public abstract class LazyParent extends Parent {
	protected boolean lazy = true;

	/**
	 * Starts a job, that calculates the children of this instance, and
	 * registers it to the listener.
	 */
	@Override
	public Parent[] getChildren() {
		if (lazy) {
			Job job = new TreeJob("Calculate " + this.getClass().getName(), this) {
				@Override
				public IStatus run(IProgressMonitor monitor) {
					if (monitor.isCanceled()) {
						return Status.CANCEL_STATUS;
					}
					initChildren();
					setCalculating(false);
					return Status.OK_STATUS;
				}
			};
			setPriority(job);
			JobDoneListener listener = JobDoneListener.getInstance();
			if (listener != null) {
				job.addJobChangeListener(listener);
			}
			job.schedule();
		}
		lazy = false;
		return super.getChildren();
	}
	
	/**
	 * May be overridden in order to change the priority. Should be used
	 * especially for lengthy calculations.
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
		this.children = new LinkedList<Parent>();
		initChildren();
	}
}
