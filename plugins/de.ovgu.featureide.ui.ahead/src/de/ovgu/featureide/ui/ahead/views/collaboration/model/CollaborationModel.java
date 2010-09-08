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
package de.ovgu.featureide.ui.ahead.views.collaboration.model;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;


/**
 * Contains the model for the Collaboration Diagram.
 * 
 * @author Constanze Adler
 */
public class CollaborationModel {
	
	protected HashMap<String,Class> classes;
	public LinkedList<Collaboration> collaborations;
	protected LinkedList<Role> roles;

	public CollaborationModel(){
		collaborations 	= new LinkedList<Collaboration>();
		classes 		= new HashMap<String,Class>();
		roles 			= new LinkedList<Role>();
	}
	
	public List<Class> getClasses(){
		LinkedList<Class> list = new LinkedList<Class>();
		Collection<Class> coll = classes.values();		
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

	public void removeClass(Class c) {
		classes.remove(c.getName());
	}
	
	public void removeRole(Role r) {
		roles.remove(r);
		List<Class> list = this.getClasses();
		list.get(list.indexOf(r.getParentClass())).removeRole(r);
		collaborations.get(collaborations.indexOf(r.getCollaboration())).removeRole(r);
	}
	
}