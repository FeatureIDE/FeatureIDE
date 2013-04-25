package org.deltaj.transformations.utils;

import java.util.Iterator;

public class Imploder {

	private final Iterable<?> elements;

	public Imploder(Iterable<?> elements) {

		this.elements = elements;
	}

	public String implode(String separator) {

		StringBuilder builder = new StringBuilder();

		Iterator<?> iterator = this.elements.iterator();
		if (iterator.hasNext()) {
			builder.append("" + iterator.next());
			while (iterator.hasNext()) {
				builder.append(separator);
				builder.append("" + iterator.next());
			}
		}

		return builder.toString();
	}
}
