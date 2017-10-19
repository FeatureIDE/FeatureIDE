package de.ovgu.featureide.ahead;

import de.ovgu.featureide.fm.core.FMComposerExtension;

public class AheadFMComposerExtension extends FMComposerExtension {

	/**
	 * Check for valid java identifier
	 */
	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		// An empty or null string cannot be a valid identifier
		if ((s == null) || (s.length() == 0)) {
			return false;
		}

		final char[] c = s.toCharArray();
		if (!Character.isJavaIdentifierStart(c[0])) {
			return false;
		}

		for (int i = 1; i < c.length; i++) {
			if (!Character.isJavaIdentifierPart(c[i])) {
				return false;
			}
		}

		return true;
	}

}
