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

	public final IMarkerResolution[] getResolutions(final IMarker marker) {
    	if (marker.getResource() instanceof IFolder) {
			final String message = marker.getAttribute(IMarker.MESSAGE, "");
			if (message.startsWith(IFeatureProject.MARKER_UNUSED)) {
				return new IMarkerResolution[] {new QuickFixMissingFeatures(marker)};
			} else if (message.startsWith(IFeatureProject.MARKER_FALSE_OPTIONAL)) {
				return new IMarkerResolution[] {new QuickFixFalseOptionalFeatures(marker)};
			}
    	}
    	return new IMarkerResolution[0];
    }
}
