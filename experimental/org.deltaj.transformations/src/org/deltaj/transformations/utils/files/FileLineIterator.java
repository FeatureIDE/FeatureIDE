package org.deltaj.transformations.utils.files;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.EnumSet;
import java.util.Iterator;
import org.deltaj.transformations.utils.RuntimeIOException;
import org.deltaj.transformations.utils.files.FileLineIterable.Option;

/**
 * Implements the {@link Iterator} interface to iterate over the lines of a
 * file.
 * 
 * @author Oliver Richers
 */
class FileLineIterator implements Iterator<String> {

	private final BufferedReader reader;
	private final EnumSet<Option> options;
	private String line;

	public FileLineIterator(BufferedReader reader, EnumSet<Option> options) {

		this.reader = reader;
		this.options = options;
		this.line = readLine();
	}

	@Override
	public boolean hasNext() {

		return line != null;
	}

	@Override
	public String next() {

		String currentLine = line;
		line = readLine();
		return currentLine;
	}

	@Override
	public void remove() {

		throw new UnsupportedOperationException();
	}

	private String readLine() {

		while (true) {

			String line = readLineFromReader();

			if (line == null) {
				return line;
			}

			if (options.contains(Option.TRIM_LINES)) {
				line = line.trim();
			}

			if (options.contains(Option.SKIP_EMPTY_LINES)) {
				if (line.isEmpty()) {
					continue;
				}
			}

			return line;
		}
	}

	private String readLineFromReader() {

		try {
			return reader.readLine();
		} catch (IOException exception) {
			throw new RuntimeIOException(exception);
		}
	}
}
