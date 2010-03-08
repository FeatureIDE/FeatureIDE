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
import java.util.Iterator;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 */
public class CD_Diagram {
	
	private ArrayList<CD_Class> classes;
	private ArrayList<CD_Role> roles;
	private ArrayList<CD_Collaboration> collaborations;
	private String name;
	
	public CD_Diagram(String name) {
		this.classes = new ArrayList<CD_Class>();
		this.roles = new ArrayList<CD_Role>();
		this.collaborations = new ArrayList<CD_Collaboration>();
		this.setName(name);
	}
	
	public boolean containsCollaboration(String feature) {
		Iterator<CD_Collaboration> iterator = collaborations.iterator();
		while (iterator.hasNext()) {
			if (iterator.next().getName().equals(feature))
				return true;
		}
		return false;
	}

	public CD_Collaboration findCollaboration(String colName) {
		Iterator<CD_Collaboration> iterator = collaborations.iterator();
		while (iterator.hasNext()) {
			CD_Collaboration collaboration = iterator.next();
			if (collaboration.getName().equals(colName))
				return collaboration;
		}
		return null;
	}

	public boolean containsClass(String className) {
		Iterator<CD_Class> iterator = classes.iterator();
		while (iterator.hasNext()) {
			if (iterator.next().getName().equals(className))
				return true;
		}
		return false;
	}
	
	public CD_Class findClass(String className) {
		Iterator<CD_Class> iterator = classes.iterator();
		while (iterator.hasNext()) {
			CD_Class cdClass = iterator.next();
			if (cdClass.getName().equals(className))
				return cdClass;
		}
		return null;
	}

	public boolean containsRoles(String role) {
		Iterator<CD_Role> iterator = roles.iterator();
		while (iterator.hasNext()) {
			if (iterator.next().getName().equals(role))
				return true;
		}
		return false;
	}

	public CD_Role findRole(String roleName) {
		Iterator<CD_Role> iterator = roles.iterator();
		while (iterator.hasNext()) {
			CD_Role role = iterator.next();
			if (role.getName().equals(roleName))
				return role;
		}
		return null;
	}

	public ArrayList<CD_Class> getClasses() {
		return classes;
	}

	public void setClasses(ArrayList<CD_Class> classes) {
		this.classes = classes;
	}

	public ArrayList<CD_Role> getRoles() {
		return roles;
	}

	public void setRoles(ArrayList<CD_Role> roles) {
		this.roles = roles;
	}

	public ArrayList<CD_Collaboration> getCollaborations() {
		return collaborations;
	}

	public void setCollaborations(ArrayList<CD_Collaboration> collaborations) {
		this.collaborations = collaborations;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getName() {
		return name;
	}
	
	public void print() {
		System.out.println("CollaborationDiagram: ----------------------------");
		System.out.println("name: " + this.getName());
		Iterator<CD_Collaboration> iteratorCol = collaborations.iterator();
		while (iteratorCol.hasNext()) {
			CD_Collaboration col = iteratorCol.next();
			System.out.println("  Collaborations: " + col.getName());
			Iterator<CD_Role> iteratorRoles = col.getRoles().iterator();
			while (iteratorRoles.hasNext())
				System.out.println("    Roles: " + iteratorRoles.next().getName());
		}

		Iterator<CD_Class> iteratorClass = classes.iterator();
		while (iteratorClass.hasNext()) {
			CD_Class cdClass = iteratorClass.next();
			System.out.println("  Classes: " + cdClass.getName());
			Iterator<CD_Role> iteratorRoles = cdClass.getRoles().iterator();
			while (iteratorRoles.hasNext()) {
				CD_Role role = iteratorRoles.next();
				System.out.println("    Roles: " + role.getName());
				System.out.println("      Roles: " + role.getContent().size());
				System.out.println("      Content: " + role.getContent());
			}
		}
		System.out.println("--------------------------------------------------");
	}

}
