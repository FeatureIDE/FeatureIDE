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
	
	public static class Arguments implements JobArguments<Boolean> {
		private final IFolder srcFolder;
		private final IFolder destFolder;
		
		public Arguments(IFolder srcFolder, IFolder destFolder) {
			this.srcFolder = srcFolder;
			this.destFolder = destFolder;
		}

		@Override
		public MPLCopyExternalJob createJob() {
			return new MPLCopyExternalJob(this);
		}
	}
	
	protected MPLCopyExternalJob(Arguments arguments) {
		super(COPYING_SOURCE_FILES, arguments);
	}

	@Override
	public Boolean execute(IMonitor workMonitor) throws Exception {
		this.workMonitor = workMonitor;
		IPath destPath = arguments.destFolder.getFullPath();
		
		try {
			IResource[] srcMembers = arguments.srcFolder.members();
			for (int i = 0; i < srcMembers.length; i++) {
				IResource srcMember = srcMembers[i];
				IPath px = destPath.append(srcMember.getName());
				if (!px.toFile().exists()) {
					srcMember.move(px, true, null);
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		MPLPlugin.getDefault().logInfo(COPIED_SOURCE_FILES_);
		return true;
	}
}
