/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.core.fstmodel.preprocessor;

import java.util.LinkedList;
import java.util.List;

import javax.annotation.CheckForNull;
import javax.annotation.Nonnull;

import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;

/**
 * Representation of a directive at a role.
 * 
 * @author Jens Meinicke
 */
public class FSTDirective extends RoleElement<FSTDirective> {

	private String expression;
	private List<String> featureNames = null;
	private FSTDirectiveCommand command;
	private LinkedList<FSTDirective> children = new LinkedList<FSTDirective>();
	private @CheckForNull FSTDirective parent;
	private int startLine;
	private int startOffset;
	private int endLine;
	private int endLength;
	private int id = -1;
	private @CheckForNull FSTRole role;

	public FSTDirective getParent() {
		return parent;
	}

	public FSTDirective() {
		super("","","");
	}

	public void setCommand(FSTDirectiveCommand command) {
		this.command = command;
	}

	public FSTDirectiveCommand getCommand() {
		return command;
	}

	public String getExpression() {
		return expression;
	}

	public void setExpression(String expression) {
		this.expression = expression;
	}

	public boolean hasChildren() {
		return !children.isEmpty();
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
	
	@Nonnull
	public LinkedList<FSTDirective> getChildrenList() {
		return children;
	}


	/**
	 * @param children the children to set
	 */
	public void setChildren(LinkedList<FSTDirective> children) {
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
		return (parent != null) ? parent.toDependencyString() : toString(0);
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
			for(FSTDirective child : children) {
				ret.append("\n");
				if (child.toString().startsWith("el")) {
					ret.append(child.toString(i));
				} else {
					ret.append(child.toString(i + 1));
				}
			}
		}
		return ret.toString();
	}

	@Override
	public String toString() {
		return interpretCommand(command) + ' ' + expression;
	}
	
	private String interpretCommand(FSTDirectiveCommand command) {
		switch (command) {
			case IF: return "if";
			case IF_NOT: return "if not";
			case IFDEF: return "ifdef";
			case IFNDEF: return "ifndef";
			case ELIF: return "elif";
			case ELIFDEF: return "elifdef";
			case ELIFNDEF: return "elifndef";
			case ELSE:
			case ELSE_NOT: return "else";
			case CONDITION: return "condition";
			case DEFINE: return "define";
			case UNDEFINE: return "undefine";
			default: return "";
			
		}
	}

	public int getColor() {
		FSTRole role2 = getRole();
		return (role2 != null && role2.getFeature() != null)
			? role2.getFeature().getColor()	: -1;
	}

	public int getStartLine() {
		return startLine;
	}

	public int getStartOffset() {
		return startOffset;
	}

	public int getEndLine() {
		return endLine;
	}

	public int getEndLength() {
		return endLength;
	}

	public void setStartLine(int startLine, int startOffset) {
		this.startLine = startLine;
		this.startOffset = startOffset;
	}

	public void setEndLine(int endLine, int endLength) {
		this.endLine = endLine;
		this.endLength = endLength;
	}

	public void setRole(FSTRole fstRole) {
		this.role = fstRole;
	}

	public FSTRole getRole() {
		return (role == null && parent != null)	? parent.getRole() : role;
	}

	public List<String> getFeatureNames() {
		return featureNames;
	}

	public void setFeatureNames(List<String> featureNames) {
		this.featureNames = featureNames;
	}

	public void setFeatureName(String featureName) {
		List<String> fN = new LinkedList<String>();
		fN.add(featureName);
		this.featureNames = fN;
	}
	
	public int getId() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}

	public String getFullName() {
		return this.toDependencyString();
	}
	
	/* 
	 * special implementation for FSTDirective by proving linenumbers 
	 **/
	@Override
	public int compareTo(FSTDirective element) {

		if (this == element) {
			return 0;
		} else {
			// TODO Is the linenumber check enough?
			return this.getStartLine() > element.getStartLine() ? 1 : -1;
		}
	}
	
}
