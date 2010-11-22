/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core;

/**
 * FeatureFormat saves all information about a file format, which is supported by FeatureIDE.
 * 
 * @author Dariusz Krolikowski
 */
public class FeatureFormat {
	private String name;
	private String template;
	private String extension;
	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}
	/**
	 * @return the template
	 */
	public String getTemplate() {
		return template;
	}
	/**
	 * @return the extension
	 */
	public String getExtension() {
		return extension;
	}
	
	public FeatureFormat(String name, String extension, String template){
		this.name = name;
		this.extension = extension;
		this.template = template;
	}
}
