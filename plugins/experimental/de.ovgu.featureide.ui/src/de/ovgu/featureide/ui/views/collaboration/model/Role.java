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

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IPath;

import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTSpecCaseSeq;

/**
 * An instance of this class represents a role. 
 * It is necessary because every figure in GEF needs an associated model.
 * 
 * @author Constanze Adler
 * @author Stephan Besecke
 */
public class Role {
	private String name;
	private Class parentClass;
	private Collaboration collaboration;
	private IPath path;
	public LinkedList<FSTField> fields = new LinkedList<FSTField>();
	public LinkedList<FSTMethod> methods = new LinkedList<FSTMethod>();	
	public LinkedList<FSTSpecCaseSeq> contracts = new LinkedList<FSTSpecCaseSeq>();
	public LinkedList<IFile> files = new LinkedList<IFile>();
	public IFile file;
	public String featureName = "";
	public boolean selected;
	public boolean isEditorFile = false;
	public LinkedList<FSTDirective> directives = new LinkedList<FSTDirective>();
	
	/**
	 * @return the path
	 */
	public IPath getPath() {
		return path;
	}

	/**
	 * @param path the path to set
	 */
	public void setPath(IPath path) {
		this.path = path;
	}

	public Role(String name){
		this.name = name;
	}
	
	/**
	 * @return String Name
	 */
	public String getName() {
		return name;
	}
	
	/**
	 * @return String Class where this role belongs to.
	 */
	public Class getParentClass(){
		return parentClass;
	}
	
	/**
	 * Setter for the role's parent Class. 
	 * Class is registered at role and role is registered at class.
	 * @param parent
	 */
	public void setParentClass(Class parent){
		this.parentClass = parent;
		parent.addRole(this);
	}
	
	/**
	 * @return Collaboration where the role belongs to.
	 */
	public Collaboration getCollaboration(){
		return this.collaboration;
	}
	
	/**
	 * Setter for the role's collaboration.
	 * Collaboration is registered at role
	 * @param c - Collaboration
	 */
	public void setCollaboration(Collaboration c){
		this.collaboration = c;
		c.addRole(this);
	}

	/**
	 * @return current file associated with the role
	 */
	public IFile getRoleFile() {
		if (path == null || !path.isAbsolute()) 
			return null;
		return file;
	}

	@Override
	public String toString() {
		if (collaboration != null) {
			return collaboration.toString() + '@' + name;
		}
		return name;
	}

}
