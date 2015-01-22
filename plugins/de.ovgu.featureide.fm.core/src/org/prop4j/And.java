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
package org.prop4j;

import java.util.ArrayList;
import java.util.List;

/**
 * A constraint that is true iff all child nodes are true.
 * 
 * @author Thomas Thuem
 */
public class And extends Node {

	public And(Object ...children) {
		setChildren(children);
	}
	
	public And(Node[] children) {
		setChildren(children);
	}

	@Override
	protected Node clausify() {
		for (int i = 0; i < children.length; i++)
			children[i] = children[i].clausify();
		fuseWithSimilarChildren();
		return this;
	}
	
	protected void collectChildren(Node node, List<Node> nodes) {
		if (node instanceof And) {
			for (Node childNode : node.getChildren()) {
				collectChildren(childNode, nodes);
			}
		} else {
			nodes.add(node);
		}
	}
	
	@Override
	public void simplify() {
		List<Node> nodes = new ArrayList<Node>();
		
		for (int i = 0; i < children.length; i++) {
			collectChildren(children[i], nodes);
		}
		
		int size = nodes.size();
		if (size != children.length) {
			Node[] newChildren = nodes.toArray(new Node[size]);
			setChildren(newChildren);
		}
		
		super.simplify();
	}
	
	@Override
	public Node clone() {
		return new And(clone(children));
	}

}
