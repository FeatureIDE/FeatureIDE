/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.ui.views.collaboration.model;


import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.TreeMap;


/**
 * Contains the model for the Collaboration Diagram.
 * 
 * @author Constanze Adler
 */
public class CollaborationModel {
	
	TreeMap<String,Class> classes;
	LinkedList<Collaboration> collaborations;
	LinkedList<Role> roles;
		
	
	public CollaborationModel(){
		collaborations 	= new LinkedList<Collaboration>();
		classes 		= new TreeMap<String,Class>();
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
	
	public void print(){
		System.out.print("\t");
		for (Class c : classes.values()){
			System.out.print(c.getName()+"\t");
		}
		System.out.println();
		for (Collaboration col: getCollaborations()){
			System.out.print(col.getName()+"\t");
			LinkedList<Role> colRoles = col.getRoles();
			for (Class c : classes.values()){
				LinkedList<Role> classRoles = c.getRoles();
				for (Role r : classRoles){
					if (colRoles.contains(r)){
						System.out.print(r.getName()+"\t");
					}
					else
						System.out.print("\t");
				}
			}
			System.out.println();
		}
	}
	
}