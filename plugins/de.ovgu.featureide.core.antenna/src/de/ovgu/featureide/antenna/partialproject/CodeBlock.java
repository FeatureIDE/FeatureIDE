/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.antenna.partialproject;

import java.util.ArrayList;

import org.prop4j.Node;

/**
 * TODO description
 *
 * @author paula
 */
public class CodeBlock {

	private final int startLine;
	private int endLine;
	private Node node;
	private final ArrayList<CodeBlock> children = new ArrayList<CodeBlock>();

	public CodeBlock() {
		startLine = 0;
	}

	protected CodeBlock(int startLine, Node node) {
		this.startLine = startLine;
		this.node = node;
	}

	public int getStartLine() {
		return startLine;
	}

	public void setEndLine(int endLine) {
		this.endLine = endLine;
	}

	public int getEndLine() {
		return endLine;
	}

	public void addChild(CodeBlock child) {
		children.add(child);
	}

	public ArrayList<CodeBlock> getChildren() {
		return children;
	}

	public Node getNode() {
		return node;
	}
}
