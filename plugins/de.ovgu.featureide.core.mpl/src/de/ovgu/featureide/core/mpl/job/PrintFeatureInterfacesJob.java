/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import static de.ovgu.featureide.fm.core.localization.StringTable.BUILT_FEATURE_INTERFACES;

import java.util.Collection;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

import de.ovgu.featureide.core.mpl.InterfaceProject;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.signature.ProjectSignatures;
import de.ovgu.featureide.core.signature.ProjectSignatures.SignatureIterator;
import de.ovgu.featureide.core.signature.ProjectStructure;
import de.ovgu.featureide.core.signature.base.AbstractClassFragment;
import de.ovgu.featureide.core.signature.filter.FeatureFilter;
import de.ovgu.featureide.fm.core.FMCorePlugin;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.io.EclipseFileSystem;
import de.ovgu.featureide.fm.core.io.FileSystem;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Builds interfaces for a single feature.
 *
 * @author Sebastian Krieter
 */
public class PrintFeatureInterfacesJob implements LongRunningMethod<Boolean> {

	private final String foldername;
	private final IProject project;

	public PrintFeatureInterfacesJob(String foldername, IProject project) {
		this.foldername = foldername;
		this.project = project;
	}

	@Override
	public Boolean execute(IMonitor<Boolean> workMonitor) throws Exception {
		final InterfaceProject interfaceProject = MPLPlugin.getDefault().getInterfaceProject(project);
		if (interfaceProject == null) {
			MPLPlugin.getDefault().logWarning(project.getName() + " is no Interface Project!");
			return false;
		}
		final ProjectSignatures projectSignatures = interfaceProject.getProjectSignatures();
		final Collection<SelectableFeature> features = interfaceProject.getConfiguration().getFeatures();

		IFolder folder = FMCorePlugin.createFolder(interfaceProject.getProjectReference(), foldername);

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

				final String path = foldername + "/" + feature.getName() + (packagename.isEmpty() ? "" : "/" + packagename);

				folder = FMCorePlugin.createFolder(interfaceProject.getProjectReference(), path);

				FileSystem.write(EclipseFileSystem.getPath(folder.getFile(role.getSignature().getName() + ".java")), role.toShortString());
			}
			workMonitor.worked();
		}
		FileSystem.write(EclipseFileSystem.getPath(interfaceProject.getProjectReference().getFile("SPL_Statistic.txt")),
				projectSignatures.getStatisticsString());
		MPLPlugin.getDefault().logInfo(BUILT_FEATURE_INTERFACES);

		return true;
	}
}
