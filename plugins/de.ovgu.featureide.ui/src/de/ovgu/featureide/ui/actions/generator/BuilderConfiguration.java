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

import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * This is just an extension of {@link Configuration} where you can define a specific name.
 *
 * @author Jens Meinicke
 */
public class BuilderConfiguration extends Configuration {

	private String name;
	private long number;

	/**
	 * @param configuration
	 */
	public BuilderConfiguration(Configuration configuration, String name) {
		super(configuration);
		this.name = name;
	}

	/**
	 * @param configuration
	 * @param number
	 */
	public BuilderConfiguration(Configuration configuration, long number) {
		super(configuration);
		this.number = number;

	}

	public void setNumber(int number) {
		this.number = number;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		if (name == null) {
			final String zeros;
			if (number < 10) {
				zeros = "0000";
			} else if (number < 100) {
				zeros = "000";
			} else if (number < 1000) {
				zeros = "00";
			} else if (number < 10000) {
				zeros = "0";
			} else {
				zeros = "";
			}
			return zeros + number;
		}
		return name;
	}

	@Override
	public String toString() {
		return getName();
	}

}
