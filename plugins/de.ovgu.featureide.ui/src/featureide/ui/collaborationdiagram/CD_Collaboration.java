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
 * contains all roles belonging to one feature
 * 
 * @author Janet Feigenspan
 */
public class CD_Collaboration {
	
	/**
	 * the name of the collaboration, i.e. the name of the feature
	 */
	private String name;
	
	private ArrayList<CD_Role> roles;
	
	public CD_Collaboration() {
		name = new String();
		roles = new ArrayList<CD_Role>();
	}
	
	public CD_Collaboration(String name, ArrayList<CD_Role> roles) {
		this.name = name;
		this.roles = roles;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}

	public void addRole(CD_Role role) {
		this.getRoles().add(role);
	}

	public void setRoles(ArrayList<CD_Role> roles) {
		this.roles = roles;
	}

	public ArrayList<CD_Role> getRoles() {
		return roles;
	}

}
