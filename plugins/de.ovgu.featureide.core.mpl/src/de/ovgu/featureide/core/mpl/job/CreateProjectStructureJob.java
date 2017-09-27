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
package de.ovgu.featureide.core.mpl.job;

import static de.ovgu.featureide.fm.core.localization.StringTable.LOADING_PROJECT_SIGNATURE;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AClassCreator;
import de.ovgu.featureide.core.signature.base.AbstractSignature;
import de.ovgu.featureide.fm.core.filter.base.IFilter;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Constructs a {@link ProjectStructure}.
 *
 * @author Sebastian Krieter
 */
public abstract class CreateProjectStructureJob extends AProjectJob<CreateProjectStructureJob.Arguments, Boolean> {

	public static class Arguments extends JobArguments {

		private final IFilter<AbstractSignature> filter;
		private final ProjectStructure projectSig;
		private final IProject project;

		public Arguments(ProjectStructure projectSig, IFilter<AbstractSignature> filter, IProject project) {
			super(Arguments.class);
			this.filter = filter;
			this.projectSig = projectSig;
			this.project = project;
		}
	}

	protected CreateProjectStructureJob(Arguments arguments) {
		super(LOADING_PROJECT_SIGNATURE, arguments);
	}

	@Override
	public Boolean execute(IMonitor workMonitor) throws Exception {
		this.workMonitor = workMonitor;
		final InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(arguments.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(arguments.project.getName() + " is no Interface Project!");
			return false;
		}
		final SignatureIterator it = interfaceProject.getProjectSignatures().iterator();
		it.addFilter(arguments.filter);
		arguments.projectSig.construct(it, getClassCreator());
		return true;
	}

	protected abstract AClassCreator getClassCreator();
}
