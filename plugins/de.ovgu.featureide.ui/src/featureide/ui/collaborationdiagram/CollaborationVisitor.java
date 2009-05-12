package featureide.ui.collaborationdiagram;

import java.util.ArrayList;
import java.util.Iterator;

import featureide.core.projectstructure.nodetypes.Node;
import featureide.core.projectstructure.nodetypes.NonTerminalNode;
import featureide.core.projectstructure.nodetypes.ProjectTreeNode;
import featureide.core.projectstructure.nodetypes.TerminalNode;
import featureide.core.projectstructure.nodetypes.Visitor;
import featureide.core.projectstructure.trees.LeafTree;
import featureide.core.projectstructure.trees.ProjectTree;

/**
 * Builds the collaboration diagram out of the project tree
 * @author yesnice
 *
 */
public class CollaborationVisitor implements Visitor {

	private CD_Diagram collaborationDiagram;

	public CollaborationVisitor() {
	}

	// @Override
	public void visit(ProjectTreeNode projectTreeNode) {
		if (projectTreeNode.getType().equalsIgnoreCase("project")) {
			collaborationDiagram = new CD_Diagram(projectTreeNode.getName());
		} else if (projectTreeNode.getType().equalsIgnoreCase("feature")) {
			collaborationDiagram.getCollaborations().add(
					new CD_Collaboration(projectTreeNode.getName(),
							new ArrayList<CD_Role>()));
		} else if (projectTreeNode.getType().equalsIgnoreCase("file")) {
			CD_Class cdClass;
			if (!collaborationDiagram.containsClass(projectTreeNode.getName())) {
				cdClass = new CD_Class(projectTreeNode.getName(),
						new ArrayList<CD_Role>());
				collaborationDiagram.getClasses().add(
						new CD_Class(projectTreeNode.getName(),
								new ArrayList<CD_Role>()));
			} else {
				cdClass = collaborationDiagram.findClass(projectTreeNode
						.getName());
			}
			CD_Role role = new CD_Role(projectTreeNode.getParent().getName()
					+ "/" + projectTreeNode.getName(), new ArrayList<String>());
			collaborationDiagram.getRoles().add(role);
			collaborationDiagram.findClass(cdClass.getName()).addRole(role);
			collaborationDiagram.findCollaboration(
					projectTreeNode.getParent().getName()).addRole(role);
		}
	}

	private String col;
	private String cdClass;

	// @Override
	public void visit(TerminalNode terminalNode) {
		collaborationDiagram.findRole(col + "/" + cdClass).getContent().add(
				terminalNode.getContent() + "\n");
	}

	// @Override
	public void visit(NonTerminalNode nonTerminalNode) {
		if (nonTerminalNode.getType().equalsIgnoreCase("ClassDeclaration")
				|| nonTerminalNode.getType().equalsIgnoreCase("InnerClassDecl")) {
			collaborationDiagram.findRole(col + "/" + cdClass).getContent()
					.add(nonTerminalNode.getType() + ": " + nonTerminalNode.getName() + "\n");
		}
		Iterator<Node> iteratorTerminal = nonTerminalNode.getChildren()
				.iterator();
		while (iteratorTerminal.hasNext()) {
			Node node = iteratorTerminal.next();
			if (node instanceof TerminalNode)
				node.accept(this);
		}
	}

	// @Override
	public void visitTree(ProjectTree projectTree) {
		if (projectTree==null||projectTree
				.getProjectTreeNodes()==null)return;

		// traverse ProjectTreeNodes
		Iterator<ProjectTreeNode> iteratorInner = projectTree
				.getProjectTreeNodes().iterator();
		while (iteratorInner.hasNext()) {
			iteratorInner.next().accept(this);
		}

		// traverse Leaftrees
		Iterator<LeafTree> iteratorLeaf = projectTree.getLeafTrees().iterator();
		while (iteratorLeaf.hasNext()) {
			// System.out.println("type: " + iteratorLeaf.next().getParent());
			LeafTree leafTree = iteratorLeaf.next();

			col = findCollaboration((ProjectTreeNode) leafTree.getParent());
			cdClass = findClass((ProjectTreeNode) leafTree.getParent());
			Iterator<NonTerminalNode> iteratorNonTerminal = leafTree
					.getNonTerminals().iterator();
			while (iteratorNonTerminal.hasNext())
				iteratorNonTerminal.next().accept(this);
		}
	}

	private String findCollaboration(ProjectTreeNode parent) {
		if (parent.getType().equalsIgnoreCase("feature"))
			return parent.getName();
		else if (!parent.getType().equalsIgnoreCase("root"))
			return findCollaboration((ProjectTreeNode) parent.getParent());
		else
			return null;
	}

	private String findClass(ProjectTreeNode parent) {
		if (parent.getType().equalsIgnoreCase("file"))
			return parent.getName();
		else if (!parent.getType().equalsIgnoreCase("root"))
			return findClass((ProjectTreeNode) parent.getParent());
		else
			return null;
	}

	public CD_Diagram getCollaborationDiagram() {
		return collaborationDiagram;
	}

	@Override
	public void visit(LeafTree leafTreeNode) {
		// TODO Auto-generated method stub
		
	}

}
