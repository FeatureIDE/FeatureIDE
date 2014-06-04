package de.ovgu.featureide.ui.statistics.ui.helper.jobs;

import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Job for the {@code FeatureStatisticsView}.
 * <p>
 * Behaves like a normal {@link Job} but stores a {@link Parent} for the
 * calculation.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public abstract class TreeJob extends Job implements ITreeJob {
	protected Parent calculated;

	public TreeJob(String name, Parent calculated) {
		super(name);
		this.calculated = calculated;
	}
	
	public Parent getCalculated() {
		return calculated;
	}
	
	public void setCalculated(Parent calculated) {
		this.calculated = calculated;
	}
	
}
