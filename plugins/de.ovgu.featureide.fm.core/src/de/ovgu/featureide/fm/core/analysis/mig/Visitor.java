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
package de.ovgu.featureide.fm.core.analysis.mig;

public interface Visitor<T> {

	public enum VisitResult {
		Cancel, Continue, Skip, Select
	}

	/**
	 * Called when the traverser first reaches the literal via a strong path and the corresponding variable is still undefined.
	 *
	 * @param literal the literal reached
	 */
	VisitResult visitStrong(int literal);

	/**
	 * Called when the traverser first reaches the literal via a weak path and the corresponding variable is still undefined.
	 *
	 * @param literal the literal reached
	 * @return {@code true} if the corresponding variable is set to the literal, {@code false} otherwise.
	 */
	VisitResult visitWeak(int literal);

	T getResult();

}
