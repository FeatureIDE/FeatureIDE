package org.deltaj.transformations.utils;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;

public class SetFactory {

	public static <Key> Set<Key> createIdentityHashSet() {

		return Collections.newSetFromMap(MapFactory.<Key, Boolean> createIdentityHashMap());
	}

	public static <Key> TreeSet<Key> createTreeSet() {

		return new TreeSet<Key>();
	}

	public static <Key> TreeSet<Key> createTreeSet(Collection<? extends Key> keys) {

		return new TreeSet<Key>(keys);
	}

	public static <Key> TreeSet<Key> createTreeSet(Key...keys) {

		return new TreeSet<Key>(Arrays.asList(keys));
	}
}
