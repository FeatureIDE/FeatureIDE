package org.deltaj.transformations.ui.utils;

public class ExceptionUtils {

	public static String getStackTraceAsString(Throwable throwable) {

		StringBuilder builder = new StringBuilder();

		builder.append(throwable.getClass().getCanonicalName()).append(": ");
		builder.append(throwable.getLocalizedMessage()).append("\n");
		builder.append(getStackTraceAsString(throwable.getStackTrace()));
		if (throwable.getCause() != null) {
			builder.append("\nCaused by:\n").append(getStackTraceAsString(throwable.getCause()));
		}

		return builder.toString();
	}

	private static String getStackTraceAsString(StackTraceElement[] elements) {

		StringBuilder builder = new StringBuilder();

		for (StackTraceElement element: elements) {
			builder.append(element.getClassName() + "." + element.getMethodName() + "(" + element.getFileName() + ":"
					+ element.getLineNumber() + ");\n");
		}

		return builder.toString();
	}
}
