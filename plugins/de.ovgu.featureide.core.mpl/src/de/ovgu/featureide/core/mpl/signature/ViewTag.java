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
package de.ovgu.featureide.core.mpl.signature;

/**
 * Holds a view name and level.
 *
 * @author Sebastian Krieter
 */
public class ViewTag implements Comparable<ViewTag> {

	private final String name;
	private int level;

	public ViewTag(String name, int level) {
		this.name = name == null ? "" : name;
		this.level = level;
	}

	public ViewTag(String name) {
		this(name, Integer.MAX_VALUE);
	}

	public String getName() {
		return name;
	}

	public int getLevel() {
		return level;
	}

	public void scaleUp() {
		if (level < Integer.MAX_VALUE) {
			level++;
		}
	}

	public boolean matches(ViewTag otherViewTag) {
		return (otherViewTag.level <= level) && name.equals(otherViewTag.name);
	}

	public boolean matches(String name, int level) {
		return (level <= this.level) && this.name.equals(name);
	}

	@Override
	public int hashCode() {
		return (907 * name.hashCode()) - (113 * level);
	}

	@Override
	public boolean equals(Object obj) {
		final ViewTag otherViewTag = (ViewTag) obj;
		return (otherViewTag.level == level) && otherViewTag.name.equals(name);
	}

	@Override
	public String toString() {
		return name + ":" + level;
	}

	@Override
	public int compareTo(ViewTag o) {
		if (o.name.equals(name)) {
			return level - o.level;
		}
		return name.compareTo(o.name);
	}
}
