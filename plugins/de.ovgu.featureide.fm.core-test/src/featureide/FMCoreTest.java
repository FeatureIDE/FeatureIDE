/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package featureide;

import java.lang.reflect.Method;

import junit.framework.Test;
import junit.framework.TestSuite;

/**
 * The FeatureIDE test suite that should contain all available JUnit tests.
 * 
 * @author Thomas Thuem
 */
public class FMCoreTest {
	
	public static Test suite() throws ClassNotFoundException {
		TestSuite suite = new TestSuite("FeatureIDE test suite.");
		suite.addTest(getTest("featureide.fm.core.configuration.TConfiguration"));
		suite.addTest(getTest("featureide.fm.core.editing.TModelComperator"));
		return suite;
	}

	@SuppressWarnings("unchecked")
	private static Test getTest(String suiteClassName) {
		try {
			Class clazz = Class.forName(suiteClassName);
			Method suiteMethod = clazz.getMethod("suite", new Class[0]);
			return (Test) suiteMethod.invoke(null, new Object[0]);
		} catch (Exception e) {
			throw new RuntimeException("Error", e);
		}
	}

}
