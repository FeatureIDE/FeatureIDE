package org.deltaj.transformations.utils;

import java.util.List;
import java.util.Map;

public class MapUtils {

	public static <K, V> void addToListMap(Map<K, List<V>> listMap, K key, V value) {

		List<V> list = listMap.get(key);
		if (list == null) {
			listMap.put(key, list = ListFactory.createArrayList());
		}
		list.add(value);
	}

	public static <K> K getFirstKey(Map<K, ?> map) {

		if (map.isEmpty()) {
			return null;
		}

		return map.keySet().iterator().next();
	}

	public static <V> V getFirstValue(Map<?, V> map) {

		if (map.isEmpty()) {
			return null;
		}

		return map.values().iterator().next();
	}

	public static <K, V> V removeFirstValue(Map<K, V> map) {

		K firstKey = getFirstKey(map);
		return map.remove(firstKey);
	}
}
