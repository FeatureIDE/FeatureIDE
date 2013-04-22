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
package de.ovgu.featureide.ui.views.collaboration.model;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;

/**
 * Contains the model for the Collaboration Diagram.
 * 
 * @author Constanze Adler
 */
// TODO @Jens replace with FSTModel
public class CollaborationModel {
	
	protected LinkedList<Class> classes;
	public LinkedList<Collaboration> collaborations;
	protected LinkedList<Role> roles;

	public boolean containsClass(Class c) {
		for (Class cl : classes) {
			if (cl.getName().equals(c.getName())) {
				return true;
			}
		}
		return false;
	}
	
	public Class getClass(String name) {
		for (Class cl : classes) {
			if (cl.getName().equals(name)) {
				return cl;
			}
		}
		return null;
	}
	
	public void addClass(Class c) {
		if (!containsClass(c)) {
			for (Class cl : classes) {
				if (c.getName().startsWith("*.")) {
					if (cl.getName().startsWith("*.")) {
						if (cl.getName().compareToIgnoreCase(c.getName()) > 0) {
							classes.add(classes.indexOf(cl), c);
							return;
						}
					}
				} else if (cl.getName().compareToIgnoreCase(c.getName()) > 0) {
					classes.add(classes.indexOf(cl), c);
					return;
				}
			}
			classes.add(c);
		}
	}
	
	public CollaborationModel(){
		collaborations 	= new LinkedList<Collaboration>();
		classes 		= new LinkedList<Class>();
		roles 			= new LinkedList<Role>();
	}
	
	public List<Class> getClasses(){
		LinkedList<Class> list = new LinkedList<Class>();
		Collection<Class> coll = classes;		
		for (Class c : coll)
			list.add(c);
		return list;
	}
	
	public List<Collaboration> getCollaborations(){
		return collaborations;
	}
	
	public List<Role> getRoles(){
		return roles;
	}
	
	public Role getRole(IFile iFile) {
		for (Role r : getRoles()) {
			if (r.file.equals(iFile))
				return r;
		}
		
		return null;
	}

	public void removeClass(Class c) {
		classes.remove(c);
	}
	
	public void removeRole(Role r) {
		roles.remove(r);
		List<Class> list = this.getClasses();
		list.get(list.indexOf(r.getParentClass())).removeRole(r);
		collaborations.get(collaborations.indexOf(r.getCollaboration())).removeRole(r);
	}
	
}