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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import static org.junit.Assert.assertEquals;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.Test;

import de.ovgu.featureide.Commons;

public class StatisticProgramSizeNewTest {

	private final static String getContent(final String name) {
		final StringBuilder content = new StringBuilder();
		for (final File f : Commons.getStatisticsFolder().listFiles()) {
			if (f.getName().equals(name)) {
				String s;
				try (FileReader fr = new FileReader(f.getPath().toString()); BufferedReader br = new BufferedReader(fr)) {
					while ((s = br.readLine()) != null) {
						content.append(s + "\n");
					}
				} catch (final IOException e) {
					e.printStackTrace();
				}

				break;
			}
		}
		return content.toString();
	}

	@Test
	public void testGraph() throws Exception {
		final BufferedReader br = new BufferedReader(new StringReader(getContent("Graph.jak")));
		assertEquals(37, StatisticsProgramSizeNew.countLineNumber("//", "/*", "*/", br));
	}

	@Test
	public void testDaily() throws Exception {
		final BufferedReader br = new BufferedReader(new StringReader(getContent("Daily.jak")));
		assertEquals(34, StatisticsProgramSizeNew.countLineNumber("//", "/*", "*/", br));
	}

}
