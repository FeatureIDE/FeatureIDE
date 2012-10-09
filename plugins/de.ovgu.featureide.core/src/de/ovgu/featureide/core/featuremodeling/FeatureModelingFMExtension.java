package de.ovgu.featureide.core.featuremodeling;

import org.eclipse.core.resources.IProject;

import de.ovgu.featureide.fm.core.FMComposerExtension;

/**
 * FMComposerExtension for the Feature Modeling extension.
 * 
 * @author Jens Meinicke
 * @author Florian Proksch
 * @author Stefan Krueger
 */
public class FeatureModelingFMExtension extends FMComposerExtension {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.ovgu.featureide.fm.core.FMComposerExtension#performRenaming(java.lang
	 * .String, java.lang.String, org.eclipse.core.resources.IProject)
	 */
	@Override
	public boolean performRenaming(String oldName, String newName,
			IProject project) {
		return true;
	}

	@Override
	public boolean isValidFeatureName(String s) {
		if (s == null)
			return false;
		final int len = s.length();

		if (len == 0)
			return false;
		for (int i = 0; i < len; i++) {
			if (s.charAt(i) == '"' || s.charAt(i) == '(' || s.charAt(i) == ')')
				return false;
		}
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.fm.core.FMComposerExtension#hasFeaureOrder()
	 */
	@Override
	public boolean hasFeaureOrder() {
		return false;
	}
}
