/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 *
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.fm.core.base.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * List with a fixed size that wraps around if more elements are added (overwriting previously added elements).
 *
 * @author Sebastian Krieter
 */
public class RingList<T> implements Iterable<T> {

	private final List<T> ring;
	private int firstPointer;
	private final int size;

	public RingList(int size) {
		this.ring = new ArrayList<>();
		this.size = size > 0 ? size : 1;
		this.firstPointer = 0;
	}

	public void add(T element) {
		if (ring.size() < size) {
			ring.add(element);
		} else {
			ring.set(firstPointer, element);
			firstPointer = (firstPointer + 1) % size;
		}
	}

	@Override
	public Iterator<T> iterator() {
		if (ring.size() < size) {
			return ring.iterator();
		}
		return new Iterator<T>() {

			int index = firstPointer;
			int count = 0;

			@Override
			public boolean hasNext() {
				return count < ring.size();
			}

			@Override
			public T next() {
				if (!hasNext()) {
					throw new NoSuchElementException();
				}
				final T t = ring.get(index);
				index = (index + 1) % size;
				count++;
				return t;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}

	public int size() {
		return ring.size();
	}

	public T get(int k) {
		return ring.get((firstPointer + k) % size);
	}

	public T getLast() {
		return ring.get((firstPointer + (ring.size() - 2)) % size);
	}

	public T getFirst() {
		return ring.get(firstPointer);
	}

}
