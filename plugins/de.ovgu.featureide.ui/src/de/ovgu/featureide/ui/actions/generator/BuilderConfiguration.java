/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.ui.actions.generator;

import de.ovgu.featureide.fm.core.configuration.Configuration;

/**
 * This is just an extension of {@link Configuration} where you can define
 * a specific name.
 * 
 * @author Jens Meinicke
 */
public class BuilderConfiguration extends Configuration {
	
	private String name;

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
		name = zeros + number;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}
	
}
