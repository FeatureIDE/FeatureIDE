package de.ovgu.featureide.core.search;

import java.io.File;
import java.io.FileFilter;
import java.util.Collection;
import java.util.HashSet;

public class FileSystemSearch extends Search {

	private File root;
	
	public FileSystemSearch(String filter, SearchResult result){
		super(filter, result);
	}
	
	public FileSystemSearch(String filter,File workspace, SearchResult result) {
		super(filter, result);
		root = workspace;
	}

	@Override
	public boolean performSearch() {
		final Collection<File> entries = new HashSet<File>();
		entries.add(root);
		
		//loop through all files and sub-files and and look for matches
		do {
			File entry = entries.iterator().next();
			entries.remove(entry);

			entry.listFiles(new FileFilter() {

				public boolean accept(File pathname) {
					if ((pathname.isFile()) && (pathname.getName().contains(filter))) {
						// accept file
						Result entry = new Result(true, false);
						entry.setFile(pathname); 
						result.addResult(entry);

						return true;
					}
					//scan subfiles
					if (pathname.isDirectory())
						entries.add(pathname);

					return false;
				}
			});

		} while (!entries.isEmpty());

		return true;
	}

}
