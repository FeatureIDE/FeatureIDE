package de.ovgu.featureide.cloneanalysis.views;

public enum CloneAnalysisTreeColumn {
	CLONE_OR_OCCURENCE("Clone / Occurence"), SIZE("size"), LENGTH("Lines"), TOKEN_COUNT("Tokens"), FILES_AFFECTED_COUNT(
			"Files"), VARIANT_TYPE("Type"), PROJECT_FEATURE("File Path"), CODE_STRING("Code Snippet");

	private String viewString;

	private CloneAnalysisTreeColumn(String viewString) {
		this.viewString = viewString;
	}

	@Override
	public String toString() {
		return viewString;
	}

}
