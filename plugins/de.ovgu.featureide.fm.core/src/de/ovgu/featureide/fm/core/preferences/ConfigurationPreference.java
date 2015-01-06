/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.preferences;

/**
 * Preference for configuration completion.
 * 
 * @author Sebastian Krieter
 */
public class ConfigurationPreference extends Preference<Integer> {

	public static final int 
		COMPLETION_NONE = 0,
		COMPLETION_ONE_CLICK = 1,
		COMPLETION_OPEN_CLAUSES = 2;
	
	private static ConfigurationPreference INSTANCE = null;
	
	public static ConfigurationPreference getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new ConfigurationPreference();
		}
		return INSTANCE;
	}
	private ConfigurationPreference() {
		super("de.ovgu.featureide.fm.core", "configCompletion");
	}
	
	@Override
	protected Integer parse(String value) {
		return Integer.parseInt(value);
	}
	
	@Override
	public Integer getDefaultValue() {
		return COMPLETION_ONE_CLICK;
	}
	
	@Override
	protected String toString(Integer value) {
		return value.toString();
	}
}
