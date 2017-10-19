package de.ovgu.featureide.featurecpp;

import de.ovgu.featureide.fm.core.FMComposerExtension;

public class FeatureCppFMComposerExtension extends FMComposerExtension {

	/**
	 * Matches valid c identifier First character is a letter or underscore Others are letters, numbers, underscore
	 */
	public static final String FEATURE_NAME_PATTERN = "^[a-zA-Z_]\\w*$";

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATURE_NAME_PATTERN);
	}

}
