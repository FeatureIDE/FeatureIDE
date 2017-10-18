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

import org.junit.runner.notification.Failure;

import de.ovgu.featureide.ui.UIPlugin;

/**
 * Data of a test run.
 *
 * @author Jens Meinicke
 */
public class Test implements Comparable<Test> {

	final String name;
	final float time;
	final String classname;
	final Failure failure;

	public Test(final String name, final long time, final String classname) {
		this(name, time, classname, null);
	}

	public Test(final String name, final long time, final String classname, Failure failure) {
		this.name = name;
		this.time = ((float) time) / 1000;
		this.classname = classname;
		this.failure = failure;
	}

	@Override
	public int compareTo(Test other) {
		return toString().compareToIgnoreCase(other.toString());
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		System.err.println("hashCode() not implemented for " + getClass());
		UIPlugin.getDefault().logError(new Exception("hashCode() not implemented for " + getClass()));
		return 42;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object other) {
		final Test otherTest = (Test) other;
		return classname.equals(otherTest.classname) && name.equals(otherTest.name);
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return classname + "." + name;
	}
}
