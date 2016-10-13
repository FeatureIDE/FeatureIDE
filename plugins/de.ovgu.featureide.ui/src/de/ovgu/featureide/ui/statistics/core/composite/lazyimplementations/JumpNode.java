/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Node which enables jumping to the corresponding file and line
 * 
 * @author Oliver Urbaniak
 * @author Philipp Kuhn
 */
public class JumpNode extends Parent {
	
	final String classname;
	
	IFeatureProject project;

	final int lineToJump;
	
	/**
	 * Constructor {@link Parent}
	 * 
	 * @param description
	 * 			description of Node
	 * @param fstModel
	 * 			corresponding FSTModel
	 * @param className
	 * 			corresponding class
	 */
	public JumpNode(String description, IFeatureProject project, String classname) {
		this(description, "", project, classname, 1);
	}
	
	/**
	 * Constructor {@link Parent}
	 * 
	 * @param description
	 * 			description of Node
	 * @param value
	 * 			value of Node
	 * @param fstModel
	 * 			corresponding FSTModel
	 * @param className
	 * 			corresponding class
	 */
	public JumpNode(String description, Object value, IFeatureProject project, String classname) {
		this(description, value, project, classname, 1);
	}
	
	/**
	 * Constructor {@link Parent}
	 * 
	 * @param description
	 * 			description of Node
	 * @param value
	 * 			value of Node
	 * @param fstModel
	 * 			corresponding FSTModel
	 * @param className
	 * 			corresponding class
	 * @param line
	 * 			desired line to jump to when Node is clicked
	 */
	public JumpNode(String description, Object value, IFeatureProject project , String classname, int line) {
		super(description, value);
		this.project = project;
		this.classname = classname;
		lineToJump = line;
	}
	
	public IFeatureProject getFeatureProject() {
		return project;
	}
	
	public String getClassname() {
		return classname;
	}

	public int getLine() {
		return lineToJump;
	}
}
