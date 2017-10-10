package de.ovgu.featureide.featurehouse;

import de.ovgu.featureide.fm.core.FMComposerExtension;


public class FeatureHouseFMComposerExtension extends FMComposerExtension {

	public static final String FEATURE_NAME_PATTERN = "^[a-zA-Z][\\w\\.\\-]*$";

	@Override
	protected boolean isValidFeatureNameComposerSpecific(String s) {
		return s.matches(FEATURE_NAME_PATTERN);
	}

}
