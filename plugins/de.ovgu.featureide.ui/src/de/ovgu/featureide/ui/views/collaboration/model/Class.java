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

import java.util.LinkedList;

import de.ovgu.featureide.core.IFeatureProject;

/**
 * An instance of this class represents a class. 
 * It is necessary because every figure in GEF needs an associated model.
 *  
 * @author Constanze Adler
 */
public class Class {
	
	private String name;
	private LinkedList<Role> roles;
	public IFeatureProject project;
	public boolean isOpenEditor = false;
	
	public Class (String name){
		this.name = name;
		roles = new LinkedList<Role>();
	}
	
	public String getName(){
		return this.name;
	}
	
	public void addRole(Role r){
		roles.add(r);
	}
	
	public void removeRole(Role r){
		roles.remove(r);
	}
	
	public LinkedList<Role> getRoles(){
		return roles;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return name;
	}
	
}
