/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.ui.views.outline;

import java.util.ArrayList;
import java.util.Iterator;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import featureide.core.projectstructure.nodetypes.Node;
import featureide.core.projectstructure.nodetypes.NonTerminalNode;
import featureide.core.projectstructure.nodetypes.ProjectTreeNode;
import featureide.core.projectstructure.nodetypes.TerminalNode;
import featureide.core.projectstructure.nodetypes.Visitor;
import featureide.core.projectstructure.trees.ProjectTree;
import featureide.ui.UIPlugin;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 */
public class OutlineViewContentProvider extends ArrayContentProvider implements ITreeContentProvider{
	
	private IFile inputFile;
	
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof ProjectTreeNode)
			return convertToArray(((ProjectTreeNode) parentElement).getChildren());
		else if (parentElement instanceof NonTerminalNode) {
			UIPlugin.getDefault().logInfo("piep");
			return convertToArray(((NonTerminalNode) parentElement).getChildren());
		}
		else return null;
				
	}
	
	private Node[] convertToArray (ArrayList<Node> children) {
		Iterator<Node> iterator = children.iterator();
		Node [] nodes = new Node[children.size()];
		int i = 0;
		while (iterator.hasNext()) {
			nodes[i] = iterator.next();
			i++;
		}
		return nodes;
	}

	public Object getParent(Object element) {
		if (element instanceof ProjectTreeNode)
			return ((ProjectTreeNode) element).getParent();
		else if (element instanceof NonTerminalNode)
				return ((NonTerminalNode) element).getParent();
		else if (element instanceof TerminalNode)
			return ((TerminalNode)element).getParent();
		else return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof ProjectTreeNode)
			return ((ProjectTreeNode) element).hasChildren();
		else if (element instanceof NonTerminalNode)
				return ((NonTerminalNode) element).hasChildren();
		else if (element instanceof TerminalNode)
			return ((TerminalNode)element).hasChildren();
		else return false;
	}

	public Object[] getElements(Object inputElement) {
		Visitor visitor = null;
		if (inputElement instanceof ProjectTree) {
			visitor = new OutlineVisitor(this.inputFile);
			visitor.visitTree((ProjectTree)inputElement);
			Node[] nodes = ((OutlineVisitor)visitor).getCurrentFile();
			return nodes;		
		}
//		if (inputElement instanceof ProjectTree) {
//			Iterator<Node> iterator = ((ProjectTree) inputElement).iterator();
//			nodes = new Node[((ProjectTreeIterator) iterator).size()];
//			int i = 0;
//			while (iterator.hasNext()) {
//				nodes[i] = iterator.next();
//				i++;
//			}
//		}
		return null;
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		
//		System.out.println("inputChanged" + viewer.getClass());
//		System.out.println("inputChanged" + oldInput);
//		System.out.println("inputChanged" + newInput);
	}

	public void setInputFile(IFile inputFile) {
		this.inputFile = inputFile;
	}

	public IFile getInputFile() {
		return inputFile;
	}
}
