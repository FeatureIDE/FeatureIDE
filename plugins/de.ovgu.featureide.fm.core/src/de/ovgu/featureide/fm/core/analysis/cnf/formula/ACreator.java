/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf.formula;

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * Abstract creator to derive an element from a {@link FeatureModelFormula feature model}.
 *
 * @param <T> The type of the element.
 *
 * @author Sebastian Krieter
 */
public abstract class ACreator<T> {

	protected FeatureModelFormula formula;

	private Lock lock;
	private T formulaElement;

	T get() {
		lock.lock();
		try {
			if (formulaElement == null) {
				formulaElement = create();
			}
			return formulaElement;
		} finally {
			lock.unlock();
		}
	}

	void init(FeatureModelFormula formula) {
		this.formula = formula;
		this.lock = new ReentrantLock();
	}

	protected abstract T create();

	@Override
	public int hashCode() {
		return getClass().getName().hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		return (this == obj) || ((obj != null) && (getClass() == obj.getClass()));
	}

}
