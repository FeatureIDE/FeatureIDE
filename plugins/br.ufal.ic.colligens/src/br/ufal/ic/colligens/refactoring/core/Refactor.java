package br.ufal.ic.colligens.refactoring.core;

import java.util.ArrayList;
import java.util.List;


import br.ufal.ic.colligens.refactoring.tree.ArrayAccess;
import br.ufal.ic.colligens.refactoring.tree.AssignExpr;
import br.ufal.ic.colligens.refactoring.tree.AtomicNamedDeclarator;
import br.ufal.ic.colligens.refactoring.tree.CompoundStatement;
import br.ufal.ic.colligens.refactoring.tree.Constant;
import br.ufal.ic.colligens.refactoring.tree.DeclArrayAccess;
import br.ufal.ic.colligens.refactoring.tree.Declaration;
import br.ufal.ic.colligens.refactoring.tree.ExprStatement;
import br.ufal.ic.colligens.refactoring.tree.Id;
import br.ufal.ic.colligens.refactoring.tree.InitDeclaratorI;
import br.ufal.ic.colligens.refactoring.tree.Initializer;
import br.ufal.ic.colligens.refactoring.tree.IntSpecifier;
import br.ufal.ic.colligens.refactoring.tree.NAryExpr;
import br.ufal.ic.colligens.refactoring.tree.Node;
import br.ufal.ic.colligens.refactoring.tree.Opt;
import br.ufal.ic.colligens.refactoring.tree.PostfixExpr;
import br.ufal.ic.colligens.refactoring.tree.visitor.VisitorCheckConditional;

import com.rits.cloning.Cloner;

import de.fosd.typechef.featureexpr.FeatureExpr;

public class Refactor {

	private List<Opt> nodes;
	
	public List<Opt> simplifyConditionals(List<Opt> conditionals, Node node){
		for (int i = 0; i < conditionals.size(); i++){
			Opt iNode = conditionals.get(i);
			for (int j = i+1; j < conditionals.size(); j++){
				Opt jNode = conditionals.get(j);
				if (iNode.getConditional().equivalentTo(jNode.getConditional())){
					for (int z = 0; z < jNode.getChildren().size(); z++){
						Node zNode = jNode.getChildren().get(z);
						iNode.addChild(zNode);
					}
					this.removeOptChild(node, jNode);
					conditionals.remove(j);
					j--;
				}
			}
		}
		return conditionals;
	}
	
	public void removeOptChild(Node node, Opt opt){
		for (int i = 0; i < node.getChildren().size(); i++){
			Node iNode = node.getChildren().get(i);
			if (iNode.equals(opt)){
				iNode.getParent().getChildren().remove(iNode);
			} else {
				this.removeOptChild(iNode, opt);
			}
		}
	}
	
	// This method we use to refactor any node with conditionals.
	public void refactorNode (Node node){
		
		// Getting the conditionals
		List<Opt> conditionals = new Refactor().getConditionalNodes(node);
		conditionals = this.simplifyConditionals(conditionals, node);
		
		Node nodeClone1 = this.cloneNode(node);
		Node nodeClone2 = this.cloneNode(node);
		
		
		if (conditionals.size() == 1){
			
			this.removeConditionals(nodeClone1);
			this.removeConditionalsKeepingChildren(nodeClone2);
			
			conditionals.get(0).setChildren(new ArrayList<Node>());
			Opt conditionalNot = (Opt) new Refactor().cloneNode(conditionals.get(0));
			conditionalNot.setConditional(conditionalNot.getConditional().not());
			
			conditionals.get(0).addChild(nodeClone2);
			nodeClone2.setParent(conditionals.get(0));
			
			conditionalNot.addChild(nodeClone1);
			nodeClone1.setParent(conditionalNot);
			
			int index = node.getParent().getChildren().indexOf(node);
			if (index >= 0){
				node.getParent().getChildren().remove(index);
				
				node.getParent().getChildren().add((index), conditionals.get(0));
				node.getParent().getChildren().add((index+1), conditionalNot);
			}
			
		} else if (conditionals.size() == 2){
			
			Opt conditional = (Opt) this.cloneNode(conditionals.get(0));
			Opt conditionalNot = (Opt) this.cloneNode(conditionals.get(1));
			
			conditional.setChildren(new ArrayList<Node>());
			conditionalNot.setChildren(new ArrayList<Node>());
			
			this.removeConditionalsKeepingChildrenWithTheSameCondition(nodeClone2, conditional.getConditional());
			this.removeConditionals(nodeClone2);
			this.removeConditionals(nodeClone2);
			
			this.removeConditionalsKeepingChildrenWithTheSameCondition(nodeClone1, conditionalNot.getConditional());
			this.removeConditionals(nodeClone1);
			this.removeConditionals(nodeClone1);
			
			conditional.addChild(nodeClone2);
			nodeClone2.setParent(conditional);
			
			conditionalNot.addChild(nodeClone1);
			nodeClone1.setParent(conditionalNot);
			
			int index = node.getParent().getChildren().indexOf(node);
			if (index >= 0){
				node.getParent().getChildren().remove(index);
				
				node.getParent().getChildren().add((index), conditional);
				node.getParent().getChildren().add((index+1), conditionalNot);
			}
			
		} else if (conditionals.size() > 2){
			int index = node.getParent().getChildren().indexOf(node);
			if (index >= 0){
				node.getParent().getChildren().remove(index);
				
				for (int i = 0; i < conditionals.size(); i++){
					Node clone = this.cloneNode(node);
					Opt conditional = (Opt) this.cloneNode(conditionals.get(i));
					conditional.setChildren(new ArrayList<Node>());
					
					this.removeConditionalsKeepingChildrenWithTheSameCondition(clone, conditional.getConditional());
					for (int j = 0; j < conditionals.size(); j++){
						this.removeConditionals(clone);
					}
					
					conditional.addChild(clone);
					clone.setParent(conditional);
					
					node.getParent().getChildren().add((index+i), conditional);
				}
			}
			
		}
	
	}
	
	
	public boolean refactorIfConditions(Node node){
		List<Node> children = node.getChildren();
		
		Node parent = node.getParent();
		while (parent != null && !(parent instanceof CompoundStatement) ){
			parent = parent.getParent();
		}
		
		
		List<Node> parentChildren = parent.getChildren();
		
		// It checks the presence of opt nodes in the first element of the IF STMT.
		// First element only? 
		VisitorCheckConditional visitor = new VisitorCheckConditional();
		children.get(0).accept(visitor);
		
		
		// If it finds conditionals, it is an IF Condition Pattern..
		if (visitor.containConditional() && parentChildren.contains(node)){
			
			
			// Cloning the if condition twice...
			Node conditionClone = this.cloneNode(children.get(0));
			Node conditionClone2 = this.cloneNode(children.get(0));
			
			// Adding variable test as the IF STMT condition..
			children.remove(0);
			NAryExpr expr = new NAryExpr();
			
			children.add(0, expr);
			expr.setParent(node);
			
			Id id = new Id();
			id.setName("test");
			
			expr.addChild(id);
			id.setParent(expr);
			
			
			// Adding test = first condition...
			this.removeConditionals(conditionClone);
			for (int i = 0; i < conditionClone.getChildren().size(); i++){
				this.removeConditionals(conditionClone.getChildren().get(i));
			}
			// Is it really necessary?
			// Two nodes equals..
			if (conditionClone.getChildren().size() == 2){
				conditionClone.getChildren().remove(1);
			}
			
			
			Node declaration = new Refactor().createDeclarationStatement("test", new IntSpecifier(), conditionClone);
			
			// Adding the declaration STMT after the if STMT..
			int index = parentChildren.indexOf(node);
			parentChildren.add(index+1, declaration);
			declaration.setParent(node.getParent());
			
			//Second test conditional..
			List<Opt> conditionals = this.getConditionalNodes(conditionClone2);
			int extra = 2; 
			
			
			for (int i = 0; i < conditionals.size(); i++){
				NAryExpr nAryExpr = new NAryExpr();
				Id id2 = new Id();
				id2.setName("test");
				
				nAryExpr.addChild(id2);
				id2.setParent(nAryExpr);
				nAryExpr.addChild(conditionals.get(i).getChildren().get(0));
				conditionals.get(i).getChildren().get(0).setParent(nAryExpr);
				
				Node exprStmt = this.createExprStatement("test", nAryExpr);
				
				Opt conditional = conditionals.get(i);
				conditional.setChildren(new ArrayList<Node>());
				conditional.addChild(exprStmt);
				exprStmt.setParent(conditional);
				
				// Adds the second test = test && (..) after the declaration..
				parentChildren.add(index+extra, conditional);
				conditional.setParent(node.getParent());
				
				extra++;
			}
			
			
			//Put the if STMT back to place..
			parentChildren.add(index+extra, node);
			node.setParent(node.getParent());
			parentChildren.remove(index);
			
			return true;
		}
		return false;
	}
	
	// Type should be IntSpecifier, and so on..
	public Node createDeclarationStatement(String identifier, Node type, Node value){
		Declaration declaration = new Declaration();
		declaration.addChild(type);
		type.setParent(declaration);
		
		InitDeclaratorI initDeclaratorI = new InitDeclaratorI();
		AtomicNamedDeclarator atomicNamedDeclarator = new AtomicNamedDeclarator();
		declaration.addChild(initDeclaratorI);
		initDeclaratorI.setParent(declaration);
		
		initDeclaratorI.addChild(atomicNamedDeclarator);
		Id id = new Id();
		id.setName(identifier);
		
		atomicNamedDeclarator.addChild(id);
		id.setParent(atomicNamedDeclarator);
		
		Initializer initializer = new Initializer();
		
		atomicNamedDeclarator.addChild(initializer);
		initializer.setParent(atomicNamedDeclarator);
		
		initializer.addChild(value);
		value.setParent(initializer);
		
		return declaration;
	}
	
	public Node createArrayDeclarationStatement(String identifier, Node type, int maxSize){
		Declaration declaration = new Declaration();
		declaration.addChild(type);
		type.setParent(declaration);
		
		InitDeclaratorI initDeclaratorI = new InitDeclaratorI();
		AtomicNamedDeclarator atomicNamedDeclarator = new AtomicNamedDeclarator();
		declaration.addChild(initDeclaratorI);
		initDeclaratorI.setParent(declaration);
		
		initDeclaratorI.addChild(atomicNamedDeclarator);
		Id id = new Id();
		id.setName(identifier);
		
		atomicNamedDeclarator.addChild(id);
		id.setParent(atomicNamedDeclarator);
		
		DeclArrayAccess declArrayAccess = new DeclArrayAccess();
		Constant constant = new Constant();
		constant.setValue(maxSize + "");
		
		declArrayAccess.addChild(constant);
		constant.setParent(declArrayAccess);
		
		atomicNamedDeclarator.addChild(declArrayAccess);
		declArrayAccess.setParent(atomicNamedDeclarator);
		
		return declaration;
	}
	
	public Node createDeclarationStatement(String identifier, Node type){
		Declaration declaration = new Declaration();
		declaration.addChild(type);
		type.setParent(declaration);
		
		InitDeclaratorI initDeclaratorI = new InitDeclaratorI();
		AtomicNamedDeclarator atomicNamedDeclarator = new AtomicNamedDeclarator();
		declaration.addChild(initDeclaratorI);
		initDeclaratorI.setParent(declaration);
		
		initDeclaratorI.addChild(atomicNamedDeclarator);
		Id id = new Id();
		id.setName(identifier);
		
		atomicNamedDeclarator.addChild(id);
		id.setParent(atomicNamedDeclarator);
		
		return declaration;
	}
	
	public Node createArrayExprStatement(String identifier, String index, Node value){
		ExprStatement exprStatement = new ExprStatement();
		AssignExpr assignExpr = new AssignExpr();
		PostfixExpr postExpr = new PostfixExpr();
		
		Id id = new Id();
		id.setName(identifier);
		
		ArrayAccess arrayAccess = new ArrayAccess();
		
		Constant idIndex = new Constant();
		idIndex.setValue(index);
		
		arrayAccess.addChild(idIndex);
		idIndex.setParent(arrayAccess);
		
		postExpr.addChild(id);
		id.setParent(postExpr);
		
		postExpr.addChild(arrayAccess);
		arrayAccess.setParent(postExpr);
		
		assignExpr.addChild(postExpr);
		postExpr.setParent(assignExpr);
		
		assignExpr.addChild(value);
		value.setParent(assignExpr);
		
		assignExpr.setParent(exprStatement);
		exprStatement.addChild(assignExpr);
		
		return exprStatement;
	}
	
	public Node createExprStatement(String identifier, Node value){
		ExprStatement exprStatement = new ExprStatement();
		AssignExpr assignExpr = new AssignExpr();
		
		Id id = new Id();
		id.setName(identifier);
		
		assignExpr.addChild(id);
		assignExpr.addChild(value);
		
		id.setParent(assignExpr);
		value.setParent(assignExpr);
		
		assignExpr.setParent(exprStatement);
		
		exprStatement.addChild(assignExpr);
		
		return exprStatement;
	}
	
//	public Node returnFirstConditionals(Node node){
//		List<Node> children = node.getChildren();
//		for (int i = 0; i < children.size(); i++){
//			if (children.get(i) instanceof Opt){
//				return children.get(i);
//			} else {
//				return this.returnFirstConditionals(node.getChildren().get(i));
//			}
//		}
//		return null;
//	}
	
	public void removeConditionals(Node node){
		List<Node> children = node.getChildren();
		for (int i = 0; i < children.size(); i++){
			if (children.get(i) instanceof Opt){
				node.getChildren().remove(children.get(i));
			} else {
				this.removeConditionals(node.getChildren().get(i));
			}
		}
	}
	
	public void removeConditionalsKeepingChildren(Node node){
		List<Node> children = node.getChildren();
		for (int i = 0; i < children.size(); i++){
			if (children.get(i) instanceof Opt){
				List<Node> childChildren = children.get(i).getChildren();
				int index = children.indexOf(children.get(i));
				children.remove(index);
				for (int j = 0; j < childChildren.size(); j++){
					children.add(index, childChildren.get(j));
					childChildren.get(j).setParent(node);
					index++;
				}
			} else {
				this.removeConditionalsKeepingChildren(node.getChildren().get(i));
			}
		}
	}
	
	public void removeConditionalsKeepingChildrenWithTheSameCondition(Node node, FeatureExpr conditional){
		List<Node> children = node.getChildren();
		for (int i = 0; i < children.size(); i++){
			if (children.get(i) instanceof Opt){
				// The same condition, keep children..
				if ( ((Opt) children.get(i)).getConditional().equivalentTo(conditional)){
					List<Node> childChildren = children.get(i).getChildren();
					int index = children.indexOf(children.get(i));
					children.remove(index);
					for (int j = 0; j < childChildren.size(); j++){
						children.add(index, childChildren.get(j));
						childChildren.get(j).setParent(node);
						index++;
					}
				}
			} else {
				this.removeConditionalsKeepingChildrenWithTheSameCondition(children.get(i), conditional);
			}
		}
	}
	
	public List<Opt> getConditionalNodes(Node node){
		this.nodes = new ArrayList<Opt>();
		this.setConditionalsNodes(node);
		return this.nodes;
	}
	
//	public int getIndexFirstConditionalNode(Node node){
//		List<Node> children = node.getChildren();
//		for (int i = 0; i < children.size(); i++){
//			if (children.get(i) instanceof Opt){
//				return i;
//			}
//		}
//		return -1;
//	}
//	
//	public Opt getFirstConditionalNode(Node node){
//		List<Node> children = node.getChildren();
//		for (int i = 0; i < children.size(); i++){
//			if (children.get(i) instanceof Opt){
//				return (Opt) children.get(i);
//			}
//		}
//		return null;
//	}
	
	public void setConditionalsNodes(Node node){
		List<Node> children = node.getChildren();
		for (int i = 0; i < children.size(); i++){
			if (children.get(i) instanceof Opt){
				this.nodes.add((Opt) children.get(i));
			} else {
				this.setConditionalsNodes(node.getChildren().get(i));
			}
		}
	}
	
	public Node cloneNode(Node node){
		Cloner cloner = new Cloner();
		Node clone = (Node) cloner.deepClone(node);
		return clone;
	}
	
}
