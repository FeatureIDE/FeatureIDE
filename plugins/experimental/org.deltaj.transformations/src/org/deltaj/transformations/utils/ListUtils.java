package org.deltaj.transformations.utils;

import java.util.List;
import org.deltaj.transformations.utils.exceptions.DeltaJException;
import org.eclipse.emf.common.util.EList;

public class ListUtils {

	public static <E> boolean containsByIdentity(EList<? extends E> list, E element) {

		return findElementByIdentity(list, element) >= 0;
	}

	public static <E> void removeElementByIdentity(EList<? extends E> list, E element) {

		while (true) {
			int i = findElementByIdentity(list, element);
			if (i < 0) {
				break;
			}
			list.remove(i);
		}
	}

	public static <E> int findElementByIdentity(EList<? extends E> list, E element) {

		for (int i = 0; i < list.size(); ++i) {
			if (list.get(i) == element) {
				return i;
			}
		}

		return -1;
	}

	public static <E> void replaceElementByIdentity(EList<E> list, E oldElement, E newElement) {

		int index = findElementByIdentity(list, oldElement);

		if (index < 0) {
			throw new DeltaJException("Could not find element in list.");
		}

		list.set(index, newElement);
	}

	public static <E> List<E> subList(List<E> list, int fromIndex) {

		return list.subList(fromIndex, list.size());
	}
}
