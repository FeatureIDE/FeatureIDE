package org.deltaj.transformations.utils.files;

import java.io.File;

public class FilenameMatcher implements IFileMatcher {

	private final String filename;

	public FilenameMatcher(String filename) {

		this.filename = filename;
	}

	@Override
	public boolean matches(File file) {

		return file.getName().equals(filename);
	}
}
