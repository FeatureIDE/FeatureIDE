package org.deltaj.transformations.utils;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

public class ListFactory {

	public static <Element> ArrayList<Element> createArrayList() {

		return new ArrayList<Element>();
	}

	public static <Element> ArrayList<Element> createArrayList(Collection<Element> elements) {

		return new ArrayList<Element>(elements);
	}

	public static <Element> ArrayList<Element> createArrayList(Element...elements) {

		return new ArrayList<Element>(Arrays.asList(elements));
	}
}
