/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.mpl.job;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.job.util.AJobArguments;

/**
 * 
 * @author Sebastian Krieter
 */
public class MPLCopyExternalJob extends AMonitorJob<MPLCopyExternalJob.Arguments> {
	
	public static class Arguments extends AJobArguments {
		private final IFolder srcFolder;
		private final IFolder destFolder;
		
		public Arguments(IFolder srcFolder, IFolder destFolder) {
			super(Arguments.class);
			this.srcFolder = srcFolder;
			this.destFolder = destFolder;
		}
	}
	
	protected MPLCopyExternalJob(Arguments arguments) {
		super("Copying Source Files", arguments);
		setPriority(BUILD);
	}
	
	@Override
	protected boolean work() {
		IPath destPath = arguments.destFolder.getFullPath();
		
		try {
			IResource[] srcMembers = arguments.srcFolder.members();
			for (int i = 0; i < srcMembers.length; i++) {
				IResource srcMember = srcMembers[i];
				IPath px = destPath.append(srcMember.getName());
				if (!px.toFile().exists()) {
					srcMember.move(px, true, monitor);
				}
			}
		} catch (CoreException e) {
			MPLPlugin.getDefault().logError(e);
			return false;
		}

		MPLPlugin.getDefault().logInfo("Copied Source Files.");
		return true;
	}
}
