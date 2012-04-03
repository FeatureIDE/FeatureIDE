/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;

import de.ovgu.featureide.core.fstmodel.FSTModelElement;

/**
 * preprocessor directive in class
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class FSTDirective extends FSTModelElement {

	public int lineNumber;
	
	public IFile file = null;
	
	public int command;
	
	public String expression;
	
	private ArrayList<FSTDirective> children;

	private FSTDirective parent = null;

	public static final int IF = 1;
	public static final int IF_NOT = 2;
	public static final int IFDEF = 3;
	public static final int IFNDEF = 4;
	public static final int ELIF = 5;
	public static final int ELIFDEF = 6;
	public static final int ELIFNDEF = 7;
	public static final int ELSE = 8;
	public static final int CONDITION = 9;
	public static final int DEFINE = 10;
	public static final int UNDEFINE = 11;
	
	public FSTDirective() {
		this.lineNumber = 0;
		this.command = 0;
		this.expression = "";
		
		children = new ArrayList<FSTDirective>();
	}
	
	public FSTDirective(int lineNumber, int command, String expression){
		this.lineNumber = lineNumber;
		this.command = command;
		this.expression = expression;
		
		children = new ArrayList<FSTDirective>();
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.FSTModelElement#getParent()
	 */
	@Override
	public FSTModelElement getParent() {
		return parent;
	}


	/**
	 * @return the lineNumber
	 */
	public int getLineNumber() {
		return lineNumber;
	}


	/**
	 * @param lineNumber the lineNumber to set
	 */
	public void setLineNumber(int lineNumber) {
		this.lineNumber = lineNumber;
	}


	/**
	 * @return the command
	 */
	public int getCommand() {
		return command;
	}


	/**
	 * @param command the command to set
	 */
	public void setCommand(int command) {
		this.command = command;
	}


	/**
	 * @return the expression
	 */
	public String getExpression() {
		return expression;
	}


	/**
	 * @param expression the expression to set
	 */
	public void setExpression(String expression) {
		this.expression = expression;
	}


	/**
	 * @return the children
	 */
	public FSTDirective[] getChildren() {
		FSTDirective[] elements = new FSTDirective[children.size()];
		for(int i=0; i < children.size();i++){
			elements[i] = children.get(i);
		}
		return elements;
	}
	
	public ArrayList<FSTDirective> getChildrenList() {
		return children;
	}


	/**
	 * @param children the children to set
	 */
	public void setChildren(ArrayList<FSTDirective> children) {
		for (FSTDirective d : children) {
			d.setParent(this);
		}
		this.children = children;
	}
	
	public void addChild(FSTDirective child) {
		child.setParent(this);
		children.add(child);
	}

	/**
	 * @param parent
	 */
	private void setParent(FSTDirective parent) {
		this.parent = parent;
	}

	/**
	 * Returns a representation of the directive with its parents and children.
	 * @return
	 */
	public String toDependencyString() {
		if (parent != null) {
			return parent.toDependencyString();
		}
		return toString(0);
	}
	
	/**
	 * This is just a auxiliary function for <code>toDependencyString()</code>
	 * @param i The count of parents
	 * @return
	 */
	private String toString(int i) {
		StringBuilder ret = new StringBuilder();
		for (int j = i;j > 0;j--) {
			ret.append("     ");
		}
		ret.append(interpretCommand(command));
		ret.append(" ");
		ret.append(expression);
		if (children.size() > 0) {
			for(FSTDirective child : children){
				ret.append("\n");
				ret.append(child.toString(i + 1));
			}
		}
		return ret.toString();
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return interpretCommand(command) + ' ' + expression;
	}
	
	private String interpretCommand(int command) {
		switch (command) {
			case 1: return "if";
			case 2: return "if not";
			case 3: return "ifdef";
			case 4: return "ifndef";
			case 5: return "elif";
			case 6: return "elifdef";
			case 7: return "elifndef";
			case 8: return "else";
			case 9: return "condition";
			case 10: return "define";
			case 11: return "undefine";
			default: return "";
			
		}
	}
	
}
