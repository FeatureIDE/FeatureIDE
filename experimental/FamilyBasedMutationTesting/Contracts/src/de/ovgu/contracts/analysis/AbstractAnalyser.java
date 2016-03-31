/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.contracts.analysis;

import java.util.HashMap;
import java.util.Map;

import de.ovgu.contracts.Defaults;

/**
 * 
 * @author Jens Meinicke
 *
 */
public abstract class AbstractAnalyser implements Defaults {

	public Result runRounds() {
		int time = 0;
		boolean foundError = false;
		final String analyser = getName();
		Map<String, String> additions = new HashMap<>();
		for (int i = 0; i < ANALYSIS_ROUNDS; i++) {
			final Result res = run();
			foundError = res.foundError;
			time += res.time;
			additions = res.getAdditions();
		}
		return new Result(analyser, time / ANALYSIS_ROUNDS, foundError, additions);
	}
	
	protected final String getName() {
		return getClass().getSimpleName();
	}

	/**
	 * Executes the Analyser.
	 * @return time for analysis in ms.
	 */
	protected abstract Result run();
}
