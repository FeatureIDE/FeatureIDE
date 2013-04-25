package org.deltaj.transformations.utils.files;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.util.Arrays;
import java.util.EnumSet;
import java.util.Iterator;
import java.util.List;
import org.deltaj.transformations.utils.RuntimeIOException;

/**
 * Implements the {@link Iterable} interface to iterate over the lines of a
 * file.
 * 
 * @author Oliver Richers
 */
public class FileLineIterable implements Iterable<String> {

	private final File file;
	private final EnumSet<Option> options;

	private FileLineIterable(File file, EnumSet<Option> options) {

		this.file = file;
		this.options = options;
	}

	public static enum Option {
		TRIM_LINES,
		SKIP_EMPTY_LINES
	}

	public static FileLineIterable create(File file, Option...options) {

		List<Option> list = Arrays.asList(options);
		return new FileLineIterable(file, EnumSet.copyOf(list));
	}

	@Override
	public Iterator<String> iterator() {

		try {
			return new FileLineIterator(new BufferedReader(new FileReader(file)), options);
		} catch (FileNotFoundException exception) {
			throw new RuntimeIOException(exception);
		}
	}
}
