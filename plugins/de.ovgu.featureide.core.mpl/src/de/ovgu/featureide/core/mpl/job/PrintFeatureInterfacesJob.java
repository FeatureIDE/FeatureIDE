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

import static de.ovgu.featureide.fm.core.localization.StringTable.BUILD_FEATURE_INTERFACES;
import static de.ovgu.featureide.fm.core.localization.StringTable.BUILT_FEATURE_INTERFACES;

import java.nio.file.Paths;
import java.util.List;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 * Builds interfaces for a single feature.
 *
 * @author Sebastian Krieter
 */
public class PrintFeatureInterfacesJob extends AProjectJob<PrintFeatureInterfacesJob.Arguments, Boolean> {

	public static class Arguments extends JobArguments {

		private final String foldername;
		private final IProject project;

		public Arguments(String foldername, IProject project) {
			super(Arguments.class);
			this.foldername = foldername;
			this.project = project;
		}
	}

	protected PrintFeatureInterfacesJob(Arguments arguments) {
		super(BUILD_FEATURE_INTERFACES, arguments);
	}

	@Override
	public Boolean execute(IMonitor workMonitor) throws Exception {
		this.workMonitor = workMonitor;
		final InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(arguments.project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(arguments.project.getName() + " is no Interface Project!");
			return false;
		}
		final ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();
		final List<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

		IFolder folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), arguments.foldername);

		try {
			folder.delete(true, null);
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		workMonitor.setRemainingWork(features.size());
		final int[] curFeature = new int[1];
		final SignatureIterator it = interfaceProject.getProjectSignatures().iterator();

		for (final SelectableFeature feature : features) {
			curFeature[0] = interfaceProject.getFeatureID(feature.getName());
			it.clearFilter();
			it.addFilter(new FeatureFilter(curFeature));

			final ProjectStructure structure = new ProjectStructure(it);
			for (final AbstractClassFragment role : structure.getClasses()) {
				final String packagename = role.getSignature().getPackage();

				final String path = arguments.foldername + "/" + feature.getName() + (packagename.isEmpty() ? "" : "/" + packagename);

				folder = CorePlugin.createFolder(interfaceProject.getProjectReference(), path);

				FileSystem.write(Paths.get(folder.getFile(role.getSignature().getName() + ".java").getLocationURI()), role.toShortString());
			}
			workMonitor.worked();
		}
		FileSystem.write(Paths.get(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt").getLocationURI()),
				projectSignatures.getStatisticsString());
		MPLPlugin.getDefault().logInfo(BUILT_FEATURE_INTERFACES);

		return true;
	}
}
