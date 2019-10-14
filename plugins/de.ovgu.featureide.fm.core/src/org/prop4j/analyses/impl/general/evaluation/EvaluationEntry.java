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
package org.prop4j.analyses.impl.general.evaluation;

import java.util.ArrayList;
import java.util.List;

/**
 * TODO description
 *
 * @author Joshua
 */
public class EvaluationEntry {

	public List<Long> times;
	public int numberOfFeatures;
	public int numberOfConstraints;
	public int numberOfClauses;
	public String modelName;
	public List<String> results;

	/**
	 * @param times
	 * @param numberOfFeatures
	 * @param modelName
	 */
	public EvaluationEntry(int numberOfFeatures, int numberOfConstraints, int numberOfClauses, String modelName) {
		super();
		times = new ArrayList<>();
		results = new ArrayList<>();
		this.numberOfFeatures = numberOfFeatures;
		this.numberOfConstraints = numberOfConstraints;
		this.numberOfClauses = numberOfClauses;
		this.modelName = modelName;
	}

	public void addTime(long time) {
		times.add(time);
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		String name = modelName + ";" + numberOfFeatures + ";" + numberOfConstraints + ";" + numberOfClauses + ";";
		for (int i = 0; i < times.size(); i++) {
			name += times.get(i);
			if (i != (times.size() - 1)) {
				name += "; ";
			}
		}
		boolean equa = true;
		final String eqalString = results.get(0);
		for (int i = 1; i < results.size(); i++) {
			if (!eqalString.equals(results.get(i))) {
				equa = false;
			}
		}
		name += "; " + (equa ? "Identical" : "Mismatch");
		name += "; ";
		for (int i = 0; i < results.size(); i++) {
			name += results.get(i);
			if (i != (results.size() - 1)) {
				name += "; ";
			}
		}
		return name;
	}

}
