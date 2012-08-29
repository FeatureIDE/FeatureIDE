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

import de.ovgu.featureide.core.fstmodel.FSTFeature;
import de.ovgu.featureide.core.fstmodel.FSTModelElement;

/**
 * preprocessor directive in class
 * 
 * @author Christoph Giesel
 * @author Marcus Kamieth
 */
public class FSTDirective extends FSTModelElement {

	private int startLine;
	
	private int endLine;

	private int startOffset;
	
	private int endOffset;
	
	private ArrayList<FSTFeature> referencedFeatures = new ArrayList<FSTFeature>();
	
	public int command;
	
	public String expression;
	
	public IFile file = null;
	
	private ArrayList<FSTDirective> children = new ArrayList<FSTDirective>();

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
		this.startLine = 0;
		this.endLine = 0;
		this.startOffset = 0;
		this.command = 0;
		this.expression = "";
	}
	
	public FSTDirective(int lineNumber, int command, String expression){
		this.startLine = lineNumber;
		this.command = command;
		this.expression = expression;
	}
	
	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.fstmodel.FSTModelElement#getParent()
	 */
	@Override
	public FSTModelElement getParent() {
		return parent;
	}
	
	/**
	 * @return the startLine
	 */
	public int getStartLine() {
		return startLine;
	}

	/**
	 * @return the offset
	 */
	public int getStartOffset() {
		return startOffset;
	}

	/**
	 * @param startLine the startLine to set
	 */
	public void setStartLine(int startLine) {
		this.startLine = startLine;
	}

	/**
	 * @param startOffset the startOffset to set
	 */
	public void setStartOffset(int startOffset) {
		this.startOffset = startOffset;
	}

	/**
	 * @param startLine the startLine to set
	 * @param startOffset the offset to set
	 */
	public void setStartLine(int startLine, int startOffset) {
		this.startLine = startLine;
		this.startOffset = startOffset;
	}

	/**
	 * @return the endLine
	 */
	public int getEndLine() {
		return endLine;
	}
	
	/**
	 * @return the length
	 */
	public int getEndOffset() {
		return endOffset;
	}
	
	/**
	 * @param endLine the endLine to set
	 */
	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}

	/**
	 * @param endOffset the endOffset to set
	 */
	public void setEndOffset(int endOffset) {
		this.endOffset = endOffset;
	}

	/**
	 * @param endLine the endLine to set
	 * @param endOffset the length to set
	 */
	public void setEndLine(int endLine, int endOffset) {
		this.endLine = endLine;
		this.endOffset = endOffset;
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
	 * @return the referencedFeatures
	 */
	public ArrayList<FSTFeature> getReferencedFeatures() {
		return referencedFeatures;
	}

	/**
	 * @param referencedFeatures the referencedFeatures to set
	 */
	public void addReferencedFeature(FSTFeature feature) {
		referencedFeatures.add(feature);
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
