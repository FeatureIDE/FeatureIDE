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
package featureide.ui.collaborationdiagram;

import java.util.ArrayList;

/**
 * TODO description Constanze?
 * 
 * @author Janet Feigenspan
 */
public class CD_Role {

	/**
	 * the name of this role; composed of the feature and class it belongs to
	 */
	private String name;

	/**
	 * the content of this role, e.g. the method definition
	 */
	private ArrayList<String> content;

	public CD_Role() {
		name = new String();
		content = new ArrayList<String>();
	}

	public CD_Role(String name, ArrayList<String> content) {
		this.name = name;
		this.content = content;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void setContent(ArrayList<String> content) {
		this.content = content;
	}

	public ArrayList<String> getContent() {
		return content;
	}

}
