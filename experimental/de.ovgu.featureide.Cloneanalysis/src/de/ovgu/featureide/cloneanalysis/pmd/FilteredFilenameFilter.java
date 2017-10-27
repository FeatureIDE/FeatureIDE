package de.ovgu.featureide.cloneanalysis.pmd;

import java.io.File;
import java.io.FilenameFilter;

public class FilteredFilenameFilter implements FilenameFilter {

	private final String filteredFilename;

	public FilteredFilenameFilter(String fileName) {
		this.filteredFilename = fileName;
	}

	@Override
	public boolean accept(File dir, String name) {
		if (name.equals(filteredFilename) || new File(dir, name).isDirectory())
			return true;

		return false;
	}
}