/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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

import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Display;

import de.ovgu.featureide.fm.core.job.LongRunningJob;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * listener which reacts to a LazyParent finishing calculation
 * 
 * @author Oliver Urbaniak
 */
public class LazyJobListener extends JobChangeAdapter {

	protected final LazyParent lazyParent;
	protected final TreeViewer viewer;

	public LazyJobListener(LazyParent lParent, TreeViewer viewer) {
		this.lazyParent = lParent;
		this.viewer = viewer;
	}
	
	/** 
	 *	waits for the Lazy Parent finishing calculation and expands it 
	 *	
	 * @see org.eclipse.core.runtime.jobs.IJobChangeListener#done(org.eclipse.core.runtime.jobs.IJobChangeEvent)
	 */
	@Override
	public void done(IJobChangeEvent jobEvent) {
		if (jobEvent.getResult() == Status.OK_STATUS) {
			Job job = jobEvent.getJob();
			
			if (job instanceof LongRunningJob) {
				if (lazyParent != null && viewer != null) {
					// node has to be expanded asynchronously in order avoid invalid thread access 
					Display.getDefault().asyncExec(new Runnable() {
						@Override
						public void run() {
							viewer.setExpandedState(lazyParent, !viewer.getExpandedState(lazyParent));
						}
					});
				}
			}
		}
	}

}
