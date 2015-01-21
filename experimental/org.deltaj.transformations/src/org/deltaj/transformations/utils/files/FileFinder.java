package org.deltaj.transformations.utils.files;

import java.io.File;
import java.util.Set;
import org.deltaj.transformations.utils.SetFactory;
import org.deltaj.transformations.utils.exceptions.DeltaJException;

public class FileFinder {

	private final IFileMatcher fileMatcher;
	private final Set<File> files;

	public FileFinder(IFileMatcher fileMatcher) {

		this.fileMatcher = fileMatcher;
		this.files = SetFactory.createTreeSet();
	}

	public Set<File> findAll() {

		return findAll(".");
	}

	public Set<File> findAll(String startFolder) {

		return findAll(new File(startFolder));
	}

	public Set<File> findAll(File startFolder) {

		this.files.clear();

		findAllRecursively(startFolder);

		return files;
	}

	public File findOne() {

		findAll();

		if (files.size() > 1) {
			throw new DeltaJException("Found more than one matching file.");
		}

		return files.isEmpty()? null : files.iterator().next();
	}

	public File findOneOrThrow() {

		File file = findOne();

		if (file == null) {
			throw new DeltaJException("Could not find a matching file.");
		}

		return file;
	}

	private void findAllRecursively(File folder) {

		for (File file: folder.listFiles()) {

			if (file.isDirectory()) {
				findAllRecursively(file);
			} else if (file.isFile() && fileMatcher.matches(file)) {
				files.add(file);
			}
		}
	}
}
