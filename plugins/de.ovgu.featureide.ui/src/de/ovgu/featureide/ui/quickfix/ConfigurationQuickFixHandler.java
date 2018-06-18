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
package de.ovgu.featureide.ui.quickfix;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;

import de.ovgu.featureide.core.IFeatureProject;

/**
 * Quick fix handler for "de.ovgu.featureide.core.configurationProblemMarker".
 *
 * @author Jens Meinicke
 */
public class ConfigurationQuickFixHandler implements IMarkerResolutionGenerator {

	@Override
	public final IMarkerResolution[] getResolutions(final IMarker marker) {
		if (marker.getResource() instanceof IFolder) {
			final String message = marker.getAttribute(IMarker.MESSAGE, "");
			if (message.startsWith(IFeatureProject.MARKER_NEVER_SELECTED)) {
				return new IMarkerResolution[] { new QuickFixUnusedFeatures(marker) };
			} else if (message.startsWith(IFeatureProject.MARKER_ALWAYS_SELECTED)) {
				return new IMarkerResolution[] { new QuickFixFalseOptionalFeatures(marker) };
			}
		}
		return new IMarkerResolution[0];
	}
}
