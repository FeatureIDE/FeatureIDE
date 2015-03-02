/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.featurehouse.ui.handlers;

import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.jobs.Job;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.featurehouse.FeatureHouseComposer;
import de.ovgu.featureide.featurehouse.FeatureHouseCorePlugin;
import de.ovgu.featureide.fm.core.job.AStoppableJob;
import de.ovgu.featureide.ui.handlers.base.AFeatureProjectHandler;

/**
 * Builds the meta product via FeatureHouse. 
 *
 * @author Jens Meinicke
 * @author Sebastian Krieter
 */
public class BuildMetaProductHandler extends AFeatureProjectHandler {
	
	@Override
	protected void singleAction(final IFeatureProject featureProject) {
		if (FeatureHouseComposer.COMPOSER_ID.equals(featureProject.getComposerID())) {
			final FeatureHouseComposer featureHouseComposer = (FeatureHouseComposer) featureProject.getComposer();
			featureHouseComposer.setBuildMetaProduct(!featureHouseComposer.buildMetaProduct());
			
			final Job job = new AStoppableJob("Build meta product for project \"" + featureProject.getProjectName() + "\".") {
				@Override
				protected boolean work() throws Exception {
					try {
						featureProject.getProject().build(IncrementalProjectBuilder.FULL_BUILD, null);
					} catch (CoreException e) {
						FeatureHouseCorePlugin.getDefault().logError(e);
					}
					return true;
				}
			};
			job.setPriority(Job.LONG);
			job.schedule();
		}
	}

}
