package de.ovgu.featureide.cloneanalysis.pmd;

import java.io.File;
import java.io.FilenameFilter;

public class DefaultFilenameFilter implements FilenameFilter {

	@Override
	public boolean accept(File dir, String name) {
		if (name.endsWith(".java") || new File(dir, name).isDirectory())
			return true;

		return false;
	}
}
