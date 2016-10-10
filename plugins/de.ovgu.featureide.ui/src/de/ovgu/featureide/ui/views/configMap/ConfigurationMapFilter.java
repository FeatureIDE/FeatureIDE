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
package de.ovgu.featureide.ui.views.configMap;

/**
 * TODO description
 * 
 * @author gruppe40
 */
public abstract class ConfigurationMapFilter implements IConfigurationMapFilter{
	private String name;
	private boolean isDefault;
	
	public ConfigurationMapFilter(String name) {
		this(name, false);
	}
	
	public ConfigurationMapFilter(String name, boolean isDefault) {
		this.name = name;
		this.isDefault = isDefault;
	}
	
	public void initialize(ConfigurationMap configurationMap) {
		
	}
	
	public void setName(String name) {
		this.name = name;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter#getName()
	 */
	@Override
	public String getName() {
		return name;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.views.configMap.IConfigurationMapFilter#isDefault()
	 */
	@Override
	public boolean isDefault() {
		return isDefault;
	}

}
