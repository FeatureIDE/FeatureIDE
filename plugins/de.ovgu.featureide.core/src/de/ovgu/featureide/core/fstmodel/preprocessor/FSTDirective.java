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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.util.ArrayList;

import de.ovgu.featureide.core.fstmodel.FSTModelElement;

/**
 * preprocessor directive in class
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class FSTDirective extends FSTModelElement {

	public int lineNumber;
	
	public int command;
	
	public String expression;
	
	public ArrayList<FSTDirective> children;

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
		this.children = children;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder ret = new StringBuilder("line:"+lineNumber+" "+command+" "+expression+"\n");
		ret.append("==>\n");
		for(FSTDirective child : children){
			ret.append(child.toString());
			ret.append("\n");
		}
		ret.append("<==\n");
		return ret.toString();
	}
	
}
