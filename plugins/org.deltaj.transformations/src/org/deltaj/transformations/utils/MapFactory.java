package org.deltaj.transformations.utils;

import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.TreeMap;

public class MapFactory {

	public static <Key, Value> TreeMap<Key, Value> createTreeMap() {

		return new TreeMap<Key, Value>();
	}

	public static <Key, Value> TreeMap<Key, Value> createTreeMap(Comparator<? super Key> comparator) {

		return new TreeMap<Key, Value>(comparator);
	}

	public static <Key, Value> IdentityHashMap<Key, Value> createIdentityHashMap() {

		return new IdentityHashMap<Key, Value>();
	}
}
