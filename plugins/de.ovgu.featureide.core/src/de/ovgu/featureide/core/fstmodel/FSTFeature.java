/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.TreeMap;



/**
 * @author Constanze Adler
 * @author Tom Brosch
 * 
 */
public class FSTFeature extends FSTModelElement {
	
	private String name;
	
	private TreeMap<String, FSTClass> classes;
	/* directives maps a class name to a list of preprocessor directives
	 * which are separated into 3 parts {before feature, feature (will be formatted differently), after feature}*/
	public TreeMap<String, LinkedList<ArrayList<String>>> directives;
	
	public FSTFeature(String name) {
		this.name = name;
		setClasses(new TreeMap<String, FSTClass>());
		directives = new TreeMap<String, LinkedList<ArrayList<String>>>();
	}

	public String getName() {
		return name;
	}

	public FSTModelElement[] getChildren() {
		if (getClasses() == null) {
			return new FSTModelElement[0];
		}
		FSTClass[] elements = new FSTClass[getClasses().size()];
		int i = 0;
		for (FSTClass c : getClasses().values()) {
			elements[i++] =  c;		
		}
		return elements;
	}

	/**
	 * @param currentClass
	 */
	public void add(FSTClass currentClass) {
		getClasses().put(currentClass.getName(), currentClass);
	}

	/**
	 * @return the classes
	 */
	public TreeMap<String, FSTClass> getClasses() {
		return classes;
	}

	/**
	 * @param classes the classes to set
	 */
	public void setClasses(TreeMap<String, FSTClass> classes) {
		this.classes = classes;
	}
}
