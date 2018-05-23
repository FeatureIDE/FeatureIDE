package org.deltaj.transformations.utils.files;

import java.io.File;
import java.util.regex.Pattern;

public class FilenamePatternMatcher implements IFileMatcher {

	private final Pattern filenamePattern;

	public FilenamePatternMatcher(String filenameRegexp) {

		this.filenamePattern = Pattern.compile(filenameRegexp);
	}

	@Override
	public boolean matches(File file) {

		return filenamePattern.matcher(file.getName()).matches();
	}
}
