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

import static de.ovgu.featureide.fm.core.localization.StringTable.COPIED_SOURCE_FILES_;
import static de.ovgu.featureide.fm.core.localization.StringTable.COPYING_SOURCE_FILES;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.fm.core.job.AProjectJob;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;
import de.ovgu.featureide.fm.core.job.util.JobArguments;

/**
 *
 * @author Sebastian Krieter
 */
public class MPLCopyExternalJob extends AProjectJob<MPLCopyExternalJob.Arguments, Boolean> {

	public static class Arguments extends JobArguments {

		private final IFolder srcFolder;
		private final IFolder destFolder;

		public Arguments(IFolder srcFolder, IFolder destFolder) {
			super(Arguments.class);
			this.srcFolder = srcFolder;
			this.destFolder = destFolder;
		}
	}

	protected MPLCopyExternalJob(Arguments arguments) {
		super(COPYING_SOURCE_FILES, arguments);
	}

	@Override
	public Boolean execute(IMonitor workMonitor) throws Exception {
		this.workMonitor = workMonitor;
		final IPath destPath = arguments.destFolder.getFullPath();

		try {
			final IResource[] srcMembers = arguments.srcFolder.members();
			for (int i = 0; i < srcMembers.length; i++) {
				final IResource srcMember = srcMembers[i];
				final IPath px = destPath.append(srcMember.getName());
				if (!px.toFile().exists()) {
					srcMember.move(px, true, null);
				}
			}
		} catch (final CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		MPLPlugin.getDefault().logInfo(COPIED_SOURCE_FILES_);
		return true;
	}
}
