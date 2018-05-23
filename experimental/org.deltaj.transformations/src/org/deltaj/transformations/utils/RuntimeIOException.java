package org.deltaj.transformations.utils;

import java.io.IOException;

/**
 * A {@link RuntimeException} wrapper for the checked {@link IOException}.
 * 
 * @author Oliver Richers
 */
public class RuntimeIOException extends RuntimeException {

	private final IOException exception;

	public RuntimeIOException(IOException exception) {

		this.exception = exception;
	}

	public IOException getIOException() {

		return exception;
	}
}
