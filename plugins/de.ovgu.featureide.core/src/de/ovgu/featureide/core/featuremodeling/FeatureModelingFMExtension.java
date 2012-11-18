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

	@Override
	public boolean hasFeaureOrder() {
		return false;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.FMComposerExtension#getErroMessage()
	 */
	@Override
	public String getErroMessage() {
		return ERROR_MESSAGE_NO_COMPOSER;
	}
}
