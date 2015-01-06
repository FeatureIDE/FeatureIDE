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
package de.ovgu.featureide.core.preferences;

import de.ovgu.featureide.fm.core.preferences.Preference;

/**
 * Preference for context outline.
 * 
 * @author Sebastian Krieter
 */
public class ContextOutlinePreference extends Preference<Integer> {

	public static final int 
		CONTEXTOUTLINE_NONE = 0,
		CONTEXTOUTLINE_CONTEXT = 1,
		CONTEXTOUTLINE_CORE = 2;
	
	private static ContextOutlinePreference INSTANCE = null;
	
	public static ContextOutlinePreference getInstance() {
		if (INSTANCE == null) {
			INSTANCE = new ContextOutlinePreference();
		}
		return INSTANCE;
	}
	private ContextOutlinePreference() {
		super("de.ovgu.featureide.core", "contextOutline");
	}
	
	@Override
	protected Integer parse(String value) {
		return Integer.parseInt(value);
	}
	
	@Override
	public Integer getDefaultValue() {
		return CONTEXTOUTLINE_CONTEXT;
	}
	
	@Override
	protected String toString(Integer value) {
		return value.toString();
	}
}
