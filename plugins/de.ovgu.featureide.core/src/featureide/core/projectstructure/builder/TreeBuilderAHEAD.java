/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2010  FeatureIDE Team, University of Magdeburg
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
package featureide.core.projectstructure.builder;

import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;

import featureide.core.CorePlugin;
import featureide.core.IFeatureProject;
import featureide.core.jakprojectmodel.IClass;
import featureide.core.jakprojectmodel.IField;
import featureide.core.jakprojectmodel.IJakProjectModel;
import featureide.core.jakprojectmodel.IMethod;
import featureide.core.projectstructure.nodetypes.NonTerminalNode;
import featureide.core.projectstructure.nodetypes.ProjectTreeNode;
import featureide.core.projectstructure.nodetypes.TerminalNode;
import featureide.core.projectstructure.trees.LeafTree;
import featureide.core.projectstructure.trees.ProjectTree;

/**
 * TODO description
 * 
 * @author Janet Feigenspan
 * @deprecated
 */
public class TreeBuilderAHEAD {

	IFeatureProject featureProject;

	/**
	 * The name of the project
	 */
	private String projectName;

	/**
	 * The project Tree
	 */
	private ProjectTree projectTree;

	/**
	 * Returns the tree representing the project
	 * 
	 * @return the projectTree
	 */
	public ProjectTree getProjectTree() {
		return projectTree;
	}

	public TreeBuilderAHEAD(IFeatureProject featureProject) {
		this.featureProject = featureProject;
		projectTree = new ProjectTree();
	}

	public void buildTree() {
		// create the node that denotes the project
		insertProjectTreeNode("language", "AHEAD", projectTree.getRoot());
		projectName = featureProject.getJakProjectModel().getName();
		insertProjectTreeNode("project", projectName, projectTree.findNodeByName("AHEAD"));

		IFolder srcFolder = featureProject.getSourceFolder();
		try {
			IResource[] features = srcFolder.members();
			for (int i = 0; i < features.length; i++) {
				IResource[] files = ((IFolder) features[i]).members();
				ProjectTreeNode parent = insertProjectTreeNode("feature",
						features[i].getName(), projectTree
								.findNodeByName(projectName));
				for (int j = 0; j < files.length; j++) {
					ProjectTreeNode fileParent = insertProjectTreeNode("file",
							files[j].getName(), parent);
					LeafTree leafTree = createLeafTree(fileParent);
					projectTree.insertLeafTreeNode(leafTree, fileParent);
					leafTree.setIdentifier(fileParent.getIdentifier());
				}
			}
		} catch (CoreException e1) {
			CorePlugin.getDefault().logError(e1);
		}
		projectTree.print();
	}

	private LeafTree createLeafTree(ProjectTreeNode fileParent) {
		LeafTree leafTree = new LeafTree();
		leafTree.setParent(fileParent);
		IJakProjectModel project = featureProject.getJakProjectModel();
		IClass[] classes = project.getClasses();
		for (int i = 0; i < classes.length; i++) {
			NonTerminalNode nonTerminal = createNonTerminal(
					"ClassDeclaration", classes[i].getName());
			insertNonTerminal(leafTree, leafTree.getRoot(), nonTerminal);
			nonTerminal.setIdentifier(fileParent.getIdentifier() + "/"
							+ nonTerminal.getName());
	
			fillLeafTree(leafTree, nonTerminal, classes[i]);
		}
		return leafTree;
	}

	private LeafTree fillLeafTree(LeafTree leafTree,
			NonTerminalNode nonTerminal, IClass clazz) {
		IField[] fields = clazz.getFields();
		for (int i = 0; i < fields.length; i++) {
			insertTerminalNode(leafTree, createTerminal("Field Declaratoion",
					fields[i].getName()), nonTerminal);
		}
		IMethod[] methods = clazz.getMethods();
		for (int i = 0; i < methods.length; i++) {
			insertTerminalNode(leafTree, createTerminal("Method Declaratoion",
					methods[i].getName()), nonTerminal);
		}
		return leafTree;
	}

	// private LeafTree fillLeafTree(LeafTree leafTree,
	// NonTerminalNode nonTerminal, IJakElement[] jakElements, int i) {
	// if (i >= jakElements.length)
	// return leafTree;
	// if (jakElements[i] instanceof IField) {
	// inserTerminalNode(leafTree, createTerminal("Field", jakElements[i]
	// .getName()), nonTerminal);
	// fillLeafTree(leafTree, nonTerminal, jakElements, i++);
	// }
	// if (jakElements[i] instanceof IMethod) {
	// inserTerminalNode(leafTree, createTerminal("Method", jakElements[i]
	// .getName()), nonTerminal);
	// fillLeafTree(leafTree, nonTerminal, jakElements, i++);
	// }
	// // if (jakElements[i] instanceof IClass)
	// // if (jakElements[i].hasChildren())
	// // fillLeafTree(leafTree, jakElements[i], jakElements[i].getChildren(),
	// // 0);
	// // fillLeafTree(leafTree, nonTerminal, jakElements, i++);
	// return leafTree;
	// }

	private TerminalNode insertTerminalNode(LeafTree leafTree,
			TerminalNode node, NonTerminalNode parent) {
		leafTree.insertTerminal(node, parent);
		node.setIdentifier(node.getParent().getIdentifier() + "/"
				+ node.getName());
		return node;
	}

	private TerminalNode createTerminal(String type, String name) {
		return new TerminalNode(type, name, null);
	}

	private NonTerminalNode createNonTerminal(String type, String name) {
		return new NonTerminalNode(type, name, null);
	}

	private NonTerminalNode insertNonTerminal(LeafTree leafTree,
			NonTerminalNode parent, NonTerminalNode node) {
		if (node.getName().equals("-")) {
			node.setName("no name");
		}
		leafTree.insertNonTerminal(node, parent);
		node.setIdentifier(node.getParent().getIdentifier() + "/"
				+ node.getName());
		return node;
	}

	/**
	 * Creates a new ProjectTreeNode with the given type, name and parent and
	 * inserts it into the projectTree
	 * 
	 * @param type
	 *            the type of the new node
	 * @param name
	 *            the name of the new node
	 * @param parent
	 *            the parent of the new node
	 * @return the created ProjectTreeNode
	 */
	private ProjectTreeNode insertProjectTreeNode(String type, String name,
			ProjectTreeNode parent) {
		ProjectTreeNode node = new ProjectTreeNode(type, name, null);
		projectTree.insertProjectTreeNode(node, parent);
		node.setIdentifier(node.getParent().getIdentifier() + "/"
				+ node.getName());
		return node;
	}
}
