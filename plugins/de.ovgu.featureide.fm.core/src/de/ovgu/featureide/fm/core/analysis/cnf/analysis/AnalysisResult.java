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
package de.ovgu.featureide.fm.core.analysis.cnf.analysis;

import java.util.Arrays;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Wrapper class for an analysis result containing additional information about the performed analysis.
 *
 * @param <T> Type of the analysis result.
 *
 * @author Sebastian Krieter
 */
public class AnalysisResult<T> {

	private final String id;
	private final LiteralSet assumptions;
	private final int hashCode;
	private final T result;

	public AnalysisResult(String id, LiteralSet assumptions, T result) {
		this.id = id;
		this.assumptions = assumptions;
		this.result = result;
		this.hashCode = (31 * id.hashCode()) + Arrays.hashCode(assumptions.getLiterals());
	}

	public String getId() {
		return id;
	}

	public LiteralSet getAssumptions() {
		return assumptions;
	}

	public T getResult() {
		return result;
	}

	@Override
	public int hashCode() {
		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		final AnalysisResult<?> other = (AnalysisResult<?>) obj;
		return id.equals(other.id) && Arrays.equals(assumptions.getLiterals(), other.assumptions.getLiterals());
	}

}
