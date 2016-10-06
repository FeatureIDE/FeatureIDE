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

import org.eclipse.ui.internal.UIPlugin;

import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Node which enables jumping to the corresponding file
 * 
 * @author Oliver Urbaniak
 */
public class DirectivesLeafNode extends Parent {
	
	final String classname;
	
	final FSTModel fstModel;

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
	public DirectivesLeafNode(String description, FSTModel fstModel, String classname) {
		super(description);
		this.classname = classname;
		this.fstModel = fstModel;
		lineToJump = 1;
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
	public DirectivesLeafNode(String description, Object value, FSTModel fstModel, String classname) {
		super(description, value);
		this.classname = classname;
		this.fstModel = fstModel;
		lineToJump = 1;
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
	public DirectivesLeafNode(String description, Object value, FSTModel fstModel, String classname, int line) {
		super(description, value);
		this.classname = classname;
		this.fstModel = fstModel;
		lineToJump = line;
	}
	
	public FSTModel getFstModel() {
		return fstModel;
		
	}
	
	public String getClassname() {
		return classname;
	}

	public int getLine() {
		return lineToJump;
	}
}
