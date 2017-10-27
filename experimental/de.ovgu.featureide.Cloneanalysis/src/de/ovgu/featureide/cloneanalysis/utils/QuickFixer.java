package de.ovgu.featureide.cloneanalysis.utils;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaModelMarker;
import org.eclipse.ui.IMarkerResolution;
import org.eclipse.ui.IMarkerResolutionGenerator;
import org.eclipse.ui.IMarkerResolutionGenerator2;

public class QuickFixer implements IMarkerResolutionGenerator {

	@Override
	public IMarkerResolution[] getResolutions(IMarker mk) {

		return new IMarkerResolution[] {

				new QuickFix("Opening the corresponding clone file(s) in the Editor"),

		};
	}

	public boolean hasResolutions(IMarker marker) {
		return true;
	}

}