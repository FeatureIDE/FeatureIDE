package de.ovgu.featureide.cloneanalysis.views;

public enum CloneVariantType {
	/**
	 * Crossvariant clone, found in different projects
	 */
	CROSSPROJECT("inter-feature"), // TODO revert to "inter-project".
	/**
	 * Crossvariant clone, found in different feature folders
	 */
	CROSSFEATURE("inter-feature"),
	/**
	 * Intravariant clone. All found occurences are within the same
	 * featurefolder / project.
	 */
	INTRAVARIANT("intra-feature"),
	/**
	 * Variant type not determined (yet).
	 */
	UNDEFINED("undefined");

	private String viewString;

	private CloneVariantType(String viewString) {
		this.viewString = viewString;
	}

	@Override
	public String toString() {
		return viewString;
	}
}
