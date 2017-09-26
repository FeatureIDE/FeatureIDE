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
package de.ovgu.featureide.ui.actions.generator;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * Representation of all test runs.
 *
 * @author Jens Meinicke
 */
public class TestResults {

	final Set<String> modulTests = new HashSet<>();

	int ignored = 0;
	int errors = 0;
	int failures = 0;
	int started = 0;
	int tests = 0;

	final String project;
	final String name;

	Map<String, Map<String, Set<Test>>> testResults = Collections.synchronizedMap(new TreeMap<String, Map<String, Set<Test>>>());

	public TestResults(String project, String name) {
		this.project = project;
		this.name = name;
	}

	public void addTest(String klass, String configuration, Test test) {
		if (test.failure != null) {
			failures++;
		}
		tests++;
		if (!testResults.containsKey(klass)) {
			testResults.put(klass, new TreeMap<String, Set<Test>>());
		}

		final Map<String, Set<Test>> klassTest = testResults.get(klass);
		if (!klassTest.containsKey(configuration)) {
			klassTest.put(configuration, new TreeSet<Test>());
		}

		final Set<Test> configurationTests = klassTest.get(configuration);
		configurationTests.add(test);
	}

}
