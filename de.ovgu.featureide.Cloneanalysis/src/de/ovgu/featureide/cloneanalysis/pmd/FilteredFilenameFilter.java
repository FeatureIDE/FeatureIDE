package de.ovgu.featureide.cloneanalysis.pmd;

import java.io.File;

public class FilteredFilenameFilter extends DefaultFilenameFilter {
	
	private final String filteredFilename;
	public FilteredFilenameFilter(String fileName) {
		this.filteredFilename = fileName;
	}
	
	@Override
	public boolean accept(File dir, String name)
	{
		if (!super.accept(dir, name)) return false;
		return name.equals(filteredFilename);
	}
}