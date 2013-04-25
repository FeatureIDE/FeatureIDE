package org.deltaj.transformations.utils.exceptions;

public class DeltaJException extends RuntimeException {

	public DeltaJException(Throwable cause) {

		super(cause);
	}

	public DeltaJException(String text, Object...args) {

		super(format(text, args));
	}

	public DeltaJException(Throwable cause, String text, Object...args) {

		super(format(text, args), cause);
	}

	private static String format(String text, Object...args) {

		return args.length > 0? String.format(text, args) : text;
	}
}
