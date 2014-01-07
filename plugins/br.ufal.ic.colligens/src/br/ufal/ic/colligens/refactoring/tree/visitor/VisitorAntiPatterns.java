package br.ufal.ic.colligens.refactoring.tree.visitor;

import java.util.ArrayList;
import java.util.List;

import br.ufal.ic.colligens.refactoring.core.Refactor;
import br.ufal.ic.colligens.refactoring.tree.ArrayAccess;
import br.ufal.ic.colligens.refactoring.tree.AssignExpr;
import br.ufal.ic.colligens.refactoring.tree.AtomicAbstractDeclarator;
import br.ufal.ic.colligens.refactoring.tree.AtomicNamedDeclarator;
import br.ufal.ic.colligens.refactoring.tree.AutoSpecifier;
import br.ufal.ic.colligens.refactoring.tree.BreakStatement;
import br.ufal.ic.colligens.refactoring.tree.CaseStatement;
import br.ufal.ic.colligens.refactoring.tree.CharSpecifier;
import br.ufal.ic.colligens.refactoring.tree.Choice;
import br.ufal.ic.colligens.refactoring.tree.CompoundStatement;
import br.ufal.ic.colligens.refactoring.tree.ConditionalExpr;
import br.ufal.ic.colligens.refactoring.tree.ConstSpecifier;
import br.ufal.ic.colligens.refactoring.tree.Constant;
import br.ufal.ic.colligens.refactoring.tree.ContinueStatement;
import br.ufal.ic.colligens.refactoring.tree.DeclArrayAccess;
import br.ufal.ic.colligens.refactoring.tree.DeclIdentifierList;
import br.ufal.ic.colligens.refactoring.tree.DeclParameterDeclList;
import br.ufal.ic.colligens.refactoring.tree.Declaration;
import br.ufal.ic.colligens.refactoring.tree.DeclarationStatement;
import br.ufal.ic.colligens.refactoring.tree.DefaultStatement;
import br.ufal.ic.colligens.refactoring.tree.DefineDirective;
import br.ufal.ic.colligens.refactoring.tree.DoStatement;
import br.ufal.ic.colligens.refactoring.tree.DoubleSpecifier;
import br.ufal.ic.colligens.refactoring.tree.ElifStatement;
import br.ufal.ic.colligens.refactoring.tree.EnumSpecifier;
import br.ufal.ic.colligens.refactoring.tree.Enumerator;
import br.ufal.ic.colligens.refactoring.tree.ExprList;
import br.ufal.ic.colligens.refactoring.tree.ExprStatement;
import br.ufal.ic.colligens.refactoring.tree.ExternSpecifier;
import br.ufal.ic.colligens.refactoring.tree.FloatSpecifier;
import br.ufal.ic.colligens.refactoring.tree.ForStatement;
import br.ufal.ic.colligens.refactoring.tree.FunctionCall;
import br.ufal.ic.colligens.refactoring.tree.FunctionDef;
import br.ufal.ic.colligens.refactoring.tree.Id;
import br.ufal.ic.colligens.refactoring.tree.IfStatement;
import br.ufal.ic.colligens.refactoring.tree.InitDeclaratorI;
import br.ufal.ic.colligens.refactoring.tree.Initializer;
import br.ufal.ic.colligens.refactoring.tree.IntSpecifier;
import br.ufal.ic.colligens.refactoring.tree.LcurlyInitializer;
import br.ufal.ic.colligens.refactoring.tree.LongSpecifier;
import br.ufal.ic.colligens.refactoring.tree.NAryExpr;
import br.ufal.ic.colligens.refactoring.tree.NArySubExpr;
import br.ufal.ic.colligens.refactoring.tree.NestedNamedDeclarator;
import br.ufal.ic.colligens.refactoring.tree.Node;
import br.ufal.ic.colligens.refactoring.tree.One;
import br.ufal.ic.colligens.refactoring.tree.Opt;
import br.ufal.ic.colligens.refactoring.tree.ParameterDeclarationAD;
import br.ufal.ic.colligens.refactoring.tree.ParameterDeclarationD;
import br.ufal.ic.colligens.refactoring.tree.Pointer;
import br.ufal.ic.colligens.refactoring.tree.PointerCreationExpr;
import br.ufal.ic.colligens.refactoring.tree.PointerDerefExpr;
import br.ufal.ic.colligens.refactoring.tree.PointerPostfixSuffix;
import br.ufal.ic.colligens.refactoring.tree.PostfixExpr;
import br.ufal.ic.colligens.refactoring.tree.RegisterSpecifier;
import br.ufal.ic.colligens.refactoring.tree.ReturnStatement;
import br.ufal.ic.colligens.refactoring.tree.ShortSpecifier;
import br.ufal.ic.colligens.refactoring.tree.SimplePostfixSuffix;
import br.ufal.ic.colligens.refactoring.tree.SizeOfExprT;
import br.ufal.ic.colligens.refactoring.tree.SizeOfExprU;
import br.ufal.ic.colligens.refactoring.tree.Some;
import br.ufal.ic.colligens.refactoring.tree.StaticSpecifier;
import br.ufal.ic.colligens.refactoring.tree.StringLit;
import br.ufal.ic.colligens.refactoring.tree.StructDeclaration;
import br.ufal.ic.colligens.refactoring.tree.StructDeclarator;
import br.ufal.ic.colligens.refactoring.tree.StructOrUnionSpecifier;
import br.ufal.ic.colligens.refactoring.tree.SwitchStatement;
import br.ufal.ic.colligens.refactoring.tree.TranslationUnit;
import br.ufal.ic.colligens.refactoring.tree.TypeDefTypeSpecifier;
import br.ufal.ic.colligens.refactoring.tree.TypeName;
import br.ufal.ic.colligens.refactoring.tree.TypedefSpecifier;
import br.ufal.ic.colligens.refactoring.tree.UnaryExpr;
import br.ufal.ic.colligens.refactoring.tree.UnaryOpExpr;
import br.ufal.ic.colligens.refactoring.tree.UnsignedSpecifier;
import br.ufal.ic.colligens.refactoring.tree.VarArgs;
import br.ufal.ic.colligens.refactoring.tree.VoidSpecifier;
import br.ufal.ic.colligens.refactoring.tree.VolatileSpecifier;
import br.ufal.ic.colligens.refactoring.tree.WhileStatement;

public class VisitorAntiPatterns implements Visitor{

	private CompoundStatement firstCompoundStatement = null;
	private IfStatement previousIfStmt = null;
	private Declaration previousDeclaration = null;
	private SwitchStatement previousSwitch = null;
	
	public int ifConditions = 0;
	public int whileConditions = 0;
	
	@Override
	public void run(Choice node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(AtomicNamedDeclarator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ElifStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}

	@Override
	public void run(CompoundStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclIdentifierList node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TranslationUnit node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExprList node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(DeclParameterDeclList node) {
		
		VisitorCheckConditional conditionalChecker = new VisitorCheckConditional();
		node.accept(conditionalChecker);
		
		if (node.getParent() instanceof Opt || conditionalChecker.containConditional()){
			Node parent = node.getParent();
			
			Node decl = parent.getParent();
			while (decl != null && !(decl instanceof Declaration)){
				decl = decl.getParent();
			}
			
			if (decl instanceof Declaration){
				Declaration declaration = (Declaration) decl;
				if (!(declaration.getParent() instanceof DeclarationStatement)){
					
					Refactor refactor = new Refactor();
					refactor.refactorNode(declaration);
					
					
				}
			}
		}
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ParameterDeclarationD node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructDeclaration node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructDeclarator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AtomicAbstractDeclarator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Pointer node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ParameterDeclarationAD node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(FunctionDef node) {
		
		Refactor refactor = new Refactor();
		Node funcDefClone = refactor.cloneNode(node);
		
		funcDefClone.getChildren().remove(funcDefClone.getChildren().size()-1);
		
		VisitorCheckConditional conditionalChecker = new VisitorCheckConditional();
		funcDefClone.accept(conditionalChecker);
		
		// Alternatives function definitions..
		if (node.getParent() instanceof Opt){
			Opt parent = (Opt) node.getParent();
			
			if (parent.getParent() instanceof TranslationUnit){
				TranslationUnit tu = (TranslationUnit) parent.getParent();
				
				int index = tu.getChildren().indexOf(parent) + 1;
				
				if (index < tu.getChildren().size()){
					if (tu.getChildren().get(index) instanceof Opt){
						
						Node currentFunctionDef = parent.getChildren().get(0);
						Node nextFunctionDef = tu.getChildren().get(index).getChildren().get(0);
						
						if (currentFunctionDef instanceof FunctionDef && nextFunctionDef instanceof FunctionDef){
							Node currentCompundStmt = currentFunctionDef.getChildren().get(currentFunctionDef.getChildren().size()-1);
							Node nextCompundStmt = nextFunctionDef.getChildren().get(nextFunctionDef.getChildren().size()-1);
							// Same function body?
							if (currentCompundStmt.equals(nextCompundStmt)){
								
								// Clonning the function definitions..
								//Node currentFuncDefClone = refactor.cloneNode(node);
								//Node nextFuncDefClone = refactor.cloneNode(tu.getChildren().get(index));
								
								List<Opt> conditionals = refactor.getConditionalNodes(tu);
								
								// Removing the function definitions..
								tu.getChildren().remove(index);
								index--;
								tu.getChildren().remove(index);
								
								for (int i = 0; i < conditionals.size(); i++){
									Opt opt = conditionals.get(i);
									
									// removing the function body..
									if (opt.getChildren().get(0).getChildren().size() == 3){
										opt.getChildren().get(0).getChildren().remove(2);
									} else if (opt.getChildren().get(0).getChildren().size() == 4){
										opt.getChildren().get(0).getChildren().remove(3);
									} else if (opt.getChildren().get(0).getChildren().size() == 5){
										opt.getChildren().get(0).getChildren().remove(4);
									}
									
									DefineDirective define = new DefineDirective();
									define.setName("FUNCDEF");
									
									
									define.addChild(opt.getChildren().get(0));
									opt.getChildren().get(0).setParent(opt);
									
									opt.setChildren(new ArrayList<Node>());
									opt.addChild(define);
									define.setParent(opt);
									
									tu.getChildren().add(index, opt);
									index++;
									opt.setParent(tu);
								}
								
								Constant constant = new Constant();
								constant.setValue("FUNCDEF");
								
								tu.getChildren().add(index, constant);
								index++;
								constant.setParent(tu);
								
								tu.getChildren().add(index, currentCompundStmt);
								index++;
								currentCompundStmt.setParent(tu);
								
							}
						}
						
					}
				}
				
			}
			
		}
		
		
		// Parameters options..
		if (conditionalChecker.containConditional()){
			int index = node.getParent().getChildren().indexOf(node);
			
			if (index >= 0){
				List<Opt> conditionals = refactor.getConditionalNodes(node);
				refactor.simplifyConditionals(conditionals, node);
				
				for (int i = 0; i < conditionals.size(); i++){
					Opt optClone = (Opt) refactor.cloneNode(conditionals.get(i));
					optClone.setChildren(new ArrayList<Node>());
					
					DefineDirective define = new DefineDirective();
					define.setName("PARAM");
					
					for (int j = 0; j < conditionals.get(i).getChildren().size(); j++){
						Node child = conditionals.get(i).getChildren().get(j);
						define.addChild(child);
						child.setParent(define);
						
						if(child instanceof ParameterDeclarationD && j < (conditionals.get(i).getChildren().size()-1)){
							Constant comma = new Constant();
							comma.setValue(",");
							
							define.addChild(comma);
							comma.setParent(define);
						}
					}
					
					optClone.addChild(define);
					define.setParent(optClone);
					
					node.getParent().getChildren().add(index, optClone);
					optClone.setParent(node.getParent());
					index++;
					
				}
				
				
				Node atomicNamedDeclarator = node.getChildren().get(1);
				
				// Pattern do DIA (APP_PROCS.C)
				if (node.getChildren().get(1) instanceof VoidSpecifier){
					atomicNamedDeclarator = node.getChildren().get(2);
				}
				
				if (atomicNamedDeclarator instanceof AtomicNamedDeclarator){
					Node declParameterDeclList = atomicNamedDeclarator.getChildren().get(1);
					
					if (declParameterDeclList instanceof DeclParameterDeclList){
						
						int indexOpt = 0;
						for (int i = 0; i < declParameterDeclList.getChildren().size(); i++){
							if (declParameterDeclList.getChildren().get(i) instanceof Opt){
								indexOpt = i;
								break;
							}
						}
						
						ParameterDeclarationD paramDeclD = new ParameterDeclarationD();
						AtomicNamedDeclarator atNamed = new AtomicNamedDeclarator();
						
						Constant constant = new Constant();
						constant.setValue("PARAM");
						
						paramDeclD.addChild(constant);
						constant.setParent(paramDeclD);
						
						atNamed.addChild(paramDeclD);
						paramDeclD.setParent(atNamed);
						
						refactor.removeConditionals(declParameterDeclList);
						declParameterDeclList.getChildren().add(indexOpt, atNamed);
						atNamed.setParent(declParameterDeclList);
					} else if (atomicNamedDeclarator.getChildren().get(1) instanceof Opt){
						
						DeclParameterDeclList declList = new DeclParameterDeclList();
						
						ParameterDeclarationD paramDeclD = new ParameterDeclarationD();
						AtomicNamedDeclarator atNamed = new AtomicNamedDeclarator();
						
						Constant constant = new Constant();
						constant.setValue("PARAM");
						
						paramDeclD.addChild(constant);
						constant.setParent(paramDeclD);
						
						atNamed.addChild(paramDeclD);
						paramDeclD.setParent(atNamed);
						
						declList.addChild(paramDeclD);
						paramDeclD.setParent(declList);
						
						atomicNamedDeclarator.getChildren().add(1, declList);
						declList.setParent(atomicNamedDeclarator);
						
						refactor.removeConditionals(atomicNamedDeclarator);
						
					}
					
				}
				
				refactor.removeConditionals(node);
				
			}
			
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Opt node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Initializer node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(InitDeclaratorI node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypeName node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(One node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Some node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SimplePostfixSuffix node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PostfixExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AssignExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(IfStatement node) {
		
		
		// If Statements with optional conditions..
		Refactor refactor = new Refactor();
		refactor.refactorIfConditions(node);
		
		// If Wrappers
		if (node.getParent() instanceof Opt){
			int index = node.getParent().getParent().getChildren().indexOf(node.getParent());
			
			// Can we access the next node?
			if (index >= 0 && node.getParent().getParent().getChildren().size() > (index+1)){
				// Is it an Opt Node as well?
				if (node.getParent().getParent().getChildren().get((index+1)) instanceof Opt){
					
					Node ifClone = refactor.cloneNode(node);
					
					boolean refactorNode = false;
					
					// If statements without a compound statement..
					// Is the next optional node child equals to the if statement child?
					if (node.getChildren().get(1).getChildren().get(0).equals(node.getParent().getParent().getChildren().get((index+1)).getChildren().get(0))){
						refactorNode = true;
					}
					
					// If statements with a compound statement..
					// Current Compound Statement
					if (node.getChildren().size() > 1 && node.getChildren().get(1).getChildren().size() > 0){
						Node compoundCurrent = node.getChildren().get(1).getChildren().get(0);
						if (compoundCurrent instanceof CompoundStatement){
							Node nextCompound = node.getParent().getParent().getChildren().get((index+1)).getChildren().get(0);
							// Duplicate compound statement?
							if (compoundCurrent.equals(nextCompound)){
								refactorNode = true;
							}
						}
					}
					
					if (refactorNode){
						
						Constant constant = new Constant();
						constant.setValue("1");
						Node testDeclaration = refactor.createDeclarationStatement("test", new IntSpecifier(), constant);
						
						// Removing the first Opt node..
						node.getParent().getParent().getChildren().remove(index);
						
						// Removing the second Opt node..
						node.getParent().getParent().getChildren().remove(index);
						
						// Adding the test declaration node..
						node.getParent().getParent().getChildren().add(index, testDeclaration);
						index++;
						
						// Adding the new condition to the test variable..
						
						NAryExpr naryExpr = new NAryExpr();
						Id id2 = new Id();
						id2.setName("test");
						
						NArySubExpr subExpr = new NArySubExpr();
						subExpr.setOperator("&&");
						
						naryExpr.addChild(id2);
						id2.setParent(naryExpr);
						
						naryExpr.addChild(subExpr);
						subExpr.setParent(naryExpr);
						
						naryExpr.addChild(node.getChildren().get(0));
						node.getChildren().get(0).setParent(naryExpr);
						
						Node testAttribution = refactor.createExprStatement("test", naryExpr);
						
						Node grandParent = node.getParent().getParent();
						Opt firstOpt = (Opt) refactor.cloneNode(node.getParent());
						firstOpt.setChildren(new ArrayList<Node>());
						
						firstOpt.addChild(testAttribution);
						testAttribution.setParent(firstOpt);
						
						grandParent.getChildren().add(index, firstOpt);
						index++;
						
						// Removing the actual IF condition and adding test..
						NAryExpr expr = new NAryExpr();
						
						Id id = new Id();
						id.setName("test");
						
						expr.addChild(id);
						id.setParent(expr);
						
						ifClone.getChildren().remove(0);
						ifClone.getChildren().add(0, expr);
						expr.setParent(ifClone);
						
						node.getParent().getParent().getChildren().add(index, ifClone);
					}
					
				}
			}
		}
		
		//IF STATEMENT OPTIONS
		// Removing the duplicate code added by TypeChef..
		if (this.previousIfStmt != null ){
			
			if (this.previousIfStmt.getParent() instanceof Opt && node.getParent() instanceof Opt){
				
				// Getting compound statement of both if statements..
				Node compoundCurrent = node.getChildren().get(1).getChildren().get(0);
				Node compoundPrevious = this.previousIfStmt.getChildren().get(1).getChildren().get(0);
				
				if (compoundCurrent instanceof CompoundStatement && compoundPrevious instanceof CompoundStatement){
					
					List<Node> sameNodes = new ArrayList<Node>();
					
					List<Node> currentChildren = compoundCurrent.getChildren();
					List<Node> previousChildren = compoundPrevious.getChildren();
					
					int lastCurrentNode = currentChildren.size()-1;
					int previousNode = previousChildren.size()-1;
					
					for (int i = lastCurrentNode; i >= 0; i--){
						if (previousNode >= 0){
							if (currentChildren.get(i).equals(previousChildren.get(previousNode))){
								sameNodes.add(refactor.cloneNode(currentChildren.get(i)));
							} else {
								break;
							}
							previousNode--;
						}
					}
					
					double sameNodeSize = sameNodes.size();
					double currentNodeSize = currentChildren.size();
					
					// Are there equal nodes? At least 50%?
					if ( (sameNodeSize / currentNodeSize) >= 0.5 ){
						
						// Cleaning the first optional node and adding a new declaration..
						this.previousIfStmt.getParent().setChildren(new ArrayList<Node>());
						Node firstDeclaration = refactor.createDeclarationStatement("test", new IntSpecifier(), this.previousIfStmt.getChildren().get(0));
						this.previousIfStmt.getParent().addChild(firstDeclaration);
						
						node.getParent().setChildren(new ArrayList<Node>());
						Node secondDeclaration = refactor.createDeclarationStatement("test", new IntSpecifier(), node.getChildren().get(0));
						node.getParent().addChild(secondDeclaration);
						
						// creating the if statement with the test condition we define before..
						
						IfStatement ifStatement = new IfStatement();
						One one = new One();
						ifStatement.addChild(one);
						one.setParent(ifStatement);
						
						NAryExpr expr = new NAryExpr();
						
						Id id = new Id();
						id.setName("test");
						
						expr.addChild(id);
						id.setParent(expr);
						
						one.addChild(expr);
						expr.setParent(one);
						
						node.getParent().getParent().addChild(ifStatement);
						ifStatement.setParent(node.getParent().getParent());
					
						One one2 = new One();
						CompoundStatement compStmt = new CompoundStatement();
						one2.addChild(compStmt);
						compStmt.setParent(one2);
						
						for (int i = 0; i < sameNodes.size(); i++){
							compStmt.addChild(sameNodes.get(i));
						}
						
						ifStatement.addChild(one2);
						one2.setParent(ifStatement);
						
						
						// Adding the optional nodes to the if statement we create...
						Opt optPrevious = (Opt) refactor.cloneNode(this.previousIfStmt.getParent());
						optPrevious.setChildren(new ArrayList<Node>());
						
						for (int i = 0; i < previousChildren.size(); i++){
							if (!sameNodes.contains(previousChildren.get(i))){
								optPrevious.addChild(previousChildren.get(i));
								previousChildren.get(i).setParent(optPrevious);
							}
						}
						
						// Add to compound statement...
						compStmt.getChildren().add(0, optPrevious);
						
						Opt optCurrent = (Opt) refactor.cloneNode(node.getParent());
						optCurrent.setChildren(new ArrayList<Node>());
						for (int i = 0; i < currentChildren.size(); i++){
							if (!sameNodes.contains(currentChildren.get(i))){
								optCurrent.addChild(currentChildren.get(i));
								currentChildren.get(i).setParent(optCurrent);
							}
						}
						
						// Add to compound statement...
						compStmt.getChildren().add(1, optCurrent);
					}
					
					
				}
				
			}
			
			// Removing clone when directives end with else statement.
			Node firstParent = node.getParent();
			Node secondParent = firstParent.getParent();
			List<Node> parentChildren = firstParent.getChildren();
			if (firstParent instanceof Opt){
				
				Opt currentOpt = (Opt) firstParent;
				
				int indexOptParent = secondParent.getChildren().indexOf(firstParent);
				if (indexOptParent > 0 && secondParent.getChildren().get(indexOptParent-1) instanceof Opt){
					Opt nodeOptBefore = (Opt) secondParent.getChildren().get(indexOptParent-1);
					
					// Opposite conditions?
					if (currentOpt.getConditional().equivalentTo(nodeOptBefore.getConditional().not())){
						if (nodeOptBefore.getChildren().size() >= 1 && nodeOptBefore.getChildren().get(0) instanceof IfStatement){
							
							// Third element is an elifStmt?
							if (nodeOptBefore.getChildren().get(0).getChildren().size() >= 3){
								if (nodeOptBefore.getChildren().get(0).getChildren().get(2) instanceof ElifStatement){
									// The compound statement are the same?
									if (nodeOptBefore.getChildren().get(0).getChildren().get(2).getChildren().get(1).getChildren().get(0).getClass().getCanonicalName().equals(
											node.getChildren().get(1).getChildren().get(0).getClass().getCanonicalName())){
										
										// Remove the elifStmt
										nodeOptBefore.getChildren().get(0).getChildren().remove(2);
										
										// Remove the current Opt node parent of the if stmt node.. But add its child to its place..
										secondParent.getChildren().remove(indexOptParent);
										for (int i = 0; i < parentChildren.size(); i++){
											secondParent.getChildren().add(indexOptParent, parentChildren.get(i));
											parentChildren.get(i).setParent(secondParent);
											indexOptParent++;
										}
										
										// Changing the if Stmt condition..
										Node conditionToAdd = new Refactor().cloneNode(nodeOptBefore.getChildren().get(0).getChildren().get(0).getChildren().get(0));
										Node currentCondition = new Refactor().cloneNode(node.getChildren().get(0));
										
										
										// First declaration of test..
										NAryExpr naryExpr1 = new NAryExpr();
										
										NArySubExpr narySubExpr1 = new NArySubExpr();
										narySubExpr1.addChild(currentCondition);
										currentCondition.setParent(narySubExpr1);
										narySubExpr1.setOperator("");
										
										naryExpr1.addChild(narySubExpr1);
										narySubExpr1.setParent(naryExpr1);
										
										
										// Second declaration of test
										NAryExpr naryExpr2 = new NAryExpr();
										
										NArySubExpr narySubExpr2 = new NArySubExpr();
										narySubExpr2.addChild(conditionToAdd);
										conditionToAdd.setParent(narySubExpr2);
										narySubExpr2.setOperator("");
										
										naryExpr2.addChild(narySubExpr2);
										narySubExpr2.setParent(naryExpr2);
										
										
										
										// Adding test first declaration..
										Node declaration = new Refactor().createDeclarationStatement("test", new IntSpecifier(), naryExpr1);
										int indexCurrentIf = node.getParent().getChildren().indexOf(node);
										
										node.getParent().getChildren().add(indexCurrentIf, declaration);
										declaration.setParent(node.getParent());
										
										// Adding the second test attribution optionally..
										Opt currentOptClean = (Opt) new Refactor().cloneNode(currentOpt);
										currentOptClean.setConditional(currentOptClean.getConditional().not());
										currentOptClean.setChildren(new ArrayList<Node>());
										
										// Nary expression should be the complete condition test || conditiontoadd
										NAryExpr n = new NAryExpr();
										Id id2 = new Id();
										id2.setName("test");
										
										NArySubExpr e = new NArySubExpr();
										e.setOperator("|| !");
										
										n.addChild(id2);
										id2.setParent(n);
										n.addChild(e);
										e.setParent(n);
										n.addChild(naryExpr2);
										naryExpr2.setParent(n);
										
										Node exprStmt = new Refactor().createExprStatement("test", n);
										
										currentOptClean.addChild(exprStmt);
										exprStmt.setParent(currentOptClean);
										
										indexCurrentIf = indexCurrentIf + 1;
										node.getParent().getChildren().add( (indexCurrentIf), currentOptClean);
										currentOptClean.setParent(node.getParent());
										
										// Removing the actual IF condition and adding test..
										NAryExpr expr = new NAryExpr();
										
										Id id = new Id();
										id.setName("test");
										
										expr.addChild(id);
										id.setParent(expr);
										
										node.getChildren().remove(0);
										node.getChildren().add(0, expr);
										expr.setParent(node);
										
									}
									
								}
							}
							
						}
					}
					
					
				}
				
			}
			
			
		} else {
			this.previousIfStmt = node;
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(WhileStatement node) {
		boolean refactoringOkay = new Refactor().refactorIfConditions(node);
		
		VisitorCheckConditional visitor = new VisitorCheckConditional();
		node.getChildren().get(0).accept(visitor);
		
		if (!refactoringOkay && visitor.containConditional()){
			for (int i = 0; i < node.getChildren().size(); i++){
				
				if (node.getChildren().get(i) instanceof One){
					
					if (this.firstCompoundStatement != null){
						if (this.firstCompoundStatement.equals((CompoundStatement) node.getChildren().get(i).getChildren().get(0))){
							Refactor refactor = new Refactor();
							
							// Getting the first while.. (compound statement -> one -> while statement)
							WhileStatement firstWhileStmt = (WhileStatement) this.firstCompoundStatement.getParent().getParent();
							
							// Adding the test variable to its condition..
							Node firstWhileConditionClone = refactor.cloneNode(firstWhileStmt.getChildren().get(0));
							firstWhileStmt.getChildren().remove(0);
							NAryExpr expr = new NAryExpr();
							
							firstWhileStmt.getChildren().add(0, expr);
							expr.setParent(node);
							
							Id id = new Id();
							id.setName("test");
							
							expr.addChild(id);
							id.setParent(expr);
							
							// Removing while out of the optional node..
							Node whileParent = firstWhileStmt.getParent();
							if (whileParent instanceof Opt){
								// Index of the optional node..
								int index = whileParent.getParent().getChildren().indexOf(whileParent);
								whileParent.getParent().getChildren().add(index+1, firstWhileStmt);
								firstWhileStmt.getParent().getChildren().remove(firstWhileStmt);
								firstWhileStmt.setParent(whileParent.getParent());
								
								// Creating a declaration integer test = condition of the first while.. (before first while)
								Node declaration = new Refactor().createDeclarationStatement("test", new IntSpecifier(), firstWhileConditionClone);
								
								// Adding the declaration in the optional node..
								whileParent.getChildren().add(declaration);
								declaration.setParent(whileParent);
							
								
								
								Node conditionalSecondWhileClone = refactor.cloneNode(node.getChildren().get(0));
								List<Opt> conditionals = refactor.getConditionalNodes(conditionalSecondWhileClone);
								
								// Create another declaration test = condition of the second while without optional nodes.. (before first while)
								// Removing conditionals..
								refactor.removeConditionals(conditionalSecondWhileClone);
								for (int j = 0; j < conditionalSecondWhileClone.getChildren().size(); j++){
									refactor.removeConditionals(conditionalSecondWhileClone.getChildren().get(j));
								}
								if (conditionalSecondWhileClone.getChildren().size() == 2){
									conditionalSecondWhileClone.getChildren().remove(1);
								}
								
								Node secondWhileParent = node.getParent();
								if (secondWhileParent instanceof Opt){
									Node secondDeclaration = new Refactor().createDeclarationStatement("test", new IntSpecifier(), conditionalSecondWhileClone);
									// Remove the second while completely..
									secondWhileParent.setChildren(new ArrayList<Node>());
									secondWhileParent.addChild(secondDeclaration);
									
									// putting optional back to place
									int indexFirstWhileStmt = secondWhileParent.getParent().getChildren().indexOf(firstWhileStmt);
									secondWhileParent.getParent().getChildren().add(indexFirstWhileStmt, secondWhileParent);
									secondWhileParent.setParent(secondWhileParent.getParent());
									
									indexFirstWhileStmt = secondWhileParent.getParent().getChildren().indexOf(firstWhileStmt);
									secondWhileParent.getParent().getChildren().remove(indexFirstWhileStmt+1);
									
									
									// Create an attribution test = test && (optional conditions).. (before first while)
									NAryExpr nAryExpr = new NAryExpr();
									Id id2 = new Id();
									id2.setName("test");
									
									nAryExpr.addChild(id2);
									id2.setParent(nAryExpr);
									
									NAryExpr nAryExpr2 = new NAryExpr();
									nAryExpr2.addChild(id2);
									nAryExpr2.addChild(conditionals.get(0).getChildren().get(0));
									
									Node exprStmt = refactor.createExprStatement("test", nAryExpr2);
									conditionals.get(0).setChildren(new ArrayList<Node>());
									conditionals.get(0).addChild(exprStmt);
									exprStmt.setParent(conditionals.get(0));
									
									secondWhileParent.addChild(conditionals.get(0));
								} 
							}
						}
					} else {
						this.firstCompoundStatement = (CompoundStatement) node.getChildren().get(i).getChildren().get(0);
					}
					
					
				}
				node.getChildren().get(i).accept(this);
			}
		} else {
			for (int i = 0; i < node.getChildren().size(); i++){
				node.getChildren().get(i).accept(this);
			}
		}
	}

	@Override
	public void run(SizeOfExprT node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SizeOfExprU node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NestedNamedDeclarator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(FunctionCall node) {
		
		//ACHO QUE O EXPRSTATEMENT J� RESOLVE!!
//		VisitorCheckConditional visitor = new VisitorCheckConditional();
//		node.accept(visitor);
//		
//		
//		if (visitor.containConditional()){
//			Node exprStmt = node.getParent().getParent();
//			
//			// Getting the position of the original Expression Statement..
//			if (exprStmt instanceof ExprStatement){
//				Refactor refactor = new Refactor();
//				refactor.refactorNode(exprStmt);
//			}
//		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	
	@Override
	public void run(ExprStatement node) {
		
		VisitorCheckConditional conditionalChecker = new VisitorCheckConditional();
		node.accept(conditionalChecker);
		
		if (node.getChildren().size() > 0 && conditionalChecker.containConditional()){
			//if (node.getChildren().get(0).getChildren().size() > 1 && !(node.getChildren().get(0).getChildren().get(1) instanceof FunctionCall))
			Refactor refactor = new Refactor();
			refactor.refactorNode(node);
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypeDefTypeSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclArrayAccess node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ForStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NAryExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NArySubExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DoStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(CaseStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SwitchStatement node) {

		// Array pattern (alternative types and names)
		if (node.getParent() instanceof Opt){
			
			Refactor refactor = new Refactor();
			
			// The previous node is also as Opt node..
			Opt parent = (Opt) node.getParent();
			
			if (this.previousSwitch == null){
				this.previousSwitch = node;
			} else {
				
				if (this.previousSwitch.getParent() instanceof Opt){
					Opt previousOpt = (Opt) this.previousSwitch.getParent();
					
					Node currentOne = node.getChildren().get(node.getChildren().size()-1);
					Node previousOne = this.previousSwitch.getChildren().get(this.previousSwitch.getChildren().size()-1);
						
					if (currentOne instanceof One && previousOne instanceof One){
						Node switchClone = refactor.cloneNode(node);
						
						// removing both bodies from both conditionals..
						node.getChildren().remove(node.getChildren().size()-1);
						this.previousSwitch.getChildren().remove(this.previousSwitch.getChildren().size()-1);
						
						Node att = refactor.createExprStatement("var", parent.getChildren().get(0).getChildren().get(0));
						att.getChildren().add(0, new IntSpecifier());
						parent.setChildren(new ArrayList<Node>());
						parent.addChild(att);
						att.setParent(parent);
						
						
						Node att2 = refactor.createExprStatement("var", previousOpt.getChildren().get(0).getChildren().get(0));
						att2.getChildren().add(0, new IntSpecifier());
						previousOpt.setChildren(new ArrayList<Node>());
						previousOpt.addChild(att2);
						att2.setParent(previousOpt);
						
						
						// Adding the switch element..
						Constant cont = new Constant();
						cont.setValue("var");
						
						switchClone.getChildren().remove(0);
						switchClone.getChildren().add(0, cont);
						cont.setParent(switchClone);
						
						
						int index = parent.getParent().getChildren().indexOf(parent);
						parent.getParent().getChildren().add((index+1), switchClone);
						switchClone.setParent(parent.getParent());
						
					}
					
				}	
				
			}
		}	
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DefaultStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(DeclarationStatement node) {
		VisitorCheckFunctionCallNode visitor = new VisitorCheckFunctionCallNode();
		node.accept(visitor);
		
		if (visitor.containFunctionCall()){
			VisitorGetFunctionCallNode functionCallVisitor = new VisitorGetFunctionCallNode();
			node.accept(functionCallVisitor);
			
			FunctionCall functionCall = functionCallVisitor.getFunctionCall();
			
			VisitorCheckConditional visitorCheckCondition = new VisitorCheckConditional();
			functionCall.accept(visitorCheckCondition);
			
			Id id = null;
			
			if (visitorCheckCondition.containConditional()){
				Node declarationNode = node.getChildren().get(0);
				if (declarationNode instanceof Declaration){
					Node initDeclaratorI = declarationNode.getChildren().get(1);
					if (initDeclaratorI instanceof InitDeclaratorI){
						Node atomicNamedDeclarator = initDeclaratorI.getChildren().get(0);
						if (atomicNamedDeclarator instanceof AtomicNamedDeclarator){
							if (atomicNamedDeclarator.getChildren().get(0) instanceof Id){
								id = (Id) atomicNamedDeclarator.getChildren().get(0);
							}
						}
					}
				}
				
				Node declaration = new Refactor().createDeclarationStatement(id.getName(), new IntSpecifier());
				
				List<Node> parentChildren = node.getParent().getChildren();
				int index = parentChildren.indexOf(node);
				parentChildren.remove(index);
				
				parentChildren.add(index, declaration);
				
				// Adding the attributions..
				List<Opt> conditionals = new Refactor().getConditionalNodes(functionCall);
				
				Node postfixExpr = functionCall.getParent();
				if (postfixExpr instanceof PostfixExpr){
					ExprStatement exprStmt = new ExprStatement();
					AssignExpr assignExpr = new AssignExpr();
					
					exprStmt.addChild(assignExpr);
					assignExpr.setParent(exprStmt);
					
					assignExpr.addChild(id);
					id.setParent(assignExpr);
					Node postfixClone = new Refactor().cloneNode(postfixExpr);
					Node postfixClone2 = new Refactor().cloneNode(postfixExpr);
					
					assignExpr.addChild(postfixClone);
					postfixClone.setParent(assignExpr);
					
					new Refactor().removeConditionals(postfixClone);
					
					Opt optClone = (Opt) new Refactor().cloneNode(conditionals.get(0));
					Opt optClone2 = (Opt) new Refactor().cloneNode(conditionals.get(0));
					
					optClone.setChildren(new ArrayList<Node>());
					optClone.setConditional(optClone.getConditional().not());
					
					optClone.addChild(exprStmt);
					exprStmt.setParent(optClone);
					
					int indexDeclaration = parentChildren.indexOf(declaration);
					parentChildren.add(indexDeclaration+1, optClone);
					
					ExprStatement exprStmt2 = new ExprStatement();
					AssignExpr assignExpr2 = new AssignExpr();
					
					exprStmt2.addChild(assignExpr2);
					assignExpr2.setParent(exprStmt2);
					
					Id idClone = (Id) new Refactor().cloneNode(id);
					assignExpr2.addChild(idClone);
					idClone.setParent(assignExpr);
					
					assignExpr2.addChild(postfixClone2);
					postfixClone2.setParent(assignExpr2);
					
					optClone2.setChildren(new ArrayList<Node>());
					optClone2.setConditional(optClone2.getConditional());
					
					optClone2.addChild(exprStmt2);
					exprStmt2.setParent(optClone2);
					
					new Refactor().removeConditionalsKeepingChildren(postfixClone2);
					parentChildren.add(indexDeclaration+2, optClone2);
					
				}
			}
			
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(Declaration node) {
		
		// Array pattern (alternative types and names)
		if (node.getParent() instanceof Opt){
			
			Refactor refactor = new Refactor();
			
			// The previous node is also as Opt node..
			Opt parent = (Opt) node.getParent();
			
			if (this.previousDeclaration == null){
				this.previousDeclaration = node;
			} else {
				
				if (this.previousDeclaration.getParent() instanceof Opt){
					Opt previousOpt = (Opt) this.previousDeclaration.getParent();
					
					Node currentInitDeclaratorI = node.getChildren().get(node.getChildren().size()-1);
					Node previousInitDeclaratorI = this.previousDeclaration.getChildren().get(this.previousDeclaration.getChildren().size()-1);
					
					if (currentInitDeclaratorI.getChildren().size() > 1 && previousInitDeclaratorI.getChildren().size() > 1){
						Node currentInitializer = currentInitDeclaratorI.getChildren().get(1).getChildren().get(0);
						Node previousInitializer = previousInitDeclaratorI.getChildren().get(1).getChildren().get(0);
						
						if (currentInitializer instanceof Initializer && previousInitializer instanceof Initializer){
							Node elementsClone = refactor.cloneNode(currentInitializer.getChildren().get(0));
							
							// removing elements from both conditionals..
							currentInitializer.getChildren().remove(0);
							previousInitializer.getChildren().remove(0);
							
							DefineDirective define1 = new DefineDirective();
							define1.setName("DEFARRAY");
							for (int i = 0; i < parent.getChildren().size(); i++){
								Node child = parent.getChildren().get(i);
								define1.addChild(child);
								child.setParent(define1);
							}
							parent.setChildren(new ArrayList<Node>());
							parent.addChild(define1);
							define1.setParent(parent);
							
							DefineDirective define2 = new DefineDirective();
							define2.setName("DEFARRAY");
							for (int i = 0; i < previousOpt.getChildren().size(); i++){
								Node child = previousOpt.getChildren().get(i);
								define2.addChild(child);
								child.setParent(define2);
							}
							previousOpt.setChildren(new ArrayList<Node>());
							previousOpt.addChild(define2);
							define2.setParent(previousOpt);
							
							
							// Adding the common elements..
							Declaration decl = new Declaration();
							Constant cont = new Constant();
							cont.setValue("DEFARRAY");
							
							decl.addChild(cont);
							cont.setParent(decl);
							
							decl.addChild(elementsClone);
							elementsClone.setParent(decl);
							
							int index = parent.getParent().getChildren().indexOf(parent);
							parent.getParent().getChildren().add((index+1), decl);
							
						}
					}
					
				}	
				
			}
			
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Constant node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Id node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VoidSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(IntSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DoubleSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(UnsignedSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VolatileSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ConstSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExternSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypedefSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AutoSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(BreakStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(CharSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VarArgs node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PointerPostfixSuffix node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PointerDerefExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(UnaryExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ContinueStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(RegisterSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StaticSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(FloatSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ReturnStatement node) {
		VisitorCheckConditional conditonalChecker = new VisitorCheckConditional();
		node.accept(conditonalChecker);
		
		if (conditonalChecker.containConditional()){
			Refactor refactor = new Refactor();
			refactor.refactorNode(node);
			
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ShortSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(LongSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructOrUnionSpecifier node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(PointerCreationExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(UnaryOpExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(ArrayAccess node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(LcurlyInitializer node) {
		VisitorCheckConditional conditionalChecker = new VisitorCheckConditional();
		node.accept(conditionalChecker);
		
		if (conditionalChecker.containConditional()){
			
			Refactor refactor = new Refactor();
			//Node clone = refactor.cloneNode(node);
			
			List<Opt> conditionals = refactor.getConditionalNodes(node);
			
			for (int i = 0; i < conditionals.size(); i++){
				DefineDirective define = new DefineDirective();
				define.setName("ELEMS" + (i+1));
				
				List<Node> children = conditionals.get(i).getChildren();
				for (int j = 0; j < children.size(); j++){
					define.addChild(children.get(j));
					children.get(j).setParent(define);
				}
				Constant comma = new Constant();
				comma.setValue(",");
				define.addChild(comma);
				comma.setParent(define);
				
				conditionals.get(i).setChildren(new ArrayList<Node>());
				
				
				// Adding the ELEMS macro in the array..
				int indexOpt = conditionals.get(i).getParent().getChildren().indexOf(conditionals.get(i));
				
				Constant constant = new Constant();
				constant.setValue("ELEMS" + (i+1));
			
				conditionals.get(i).getParent().getChildren().add(indexOpt, constant);
				constant.setParent(conditionals.get(i).getParent());
				
				conditionals.get(i).getParent().getChildren().remove((indexOpt+1));
				
				// Adding the #define directive..
				conditionals.get(i).addChild(define);
				define.setParent(conditionals.get(i));
				
				Node declStmt = node.getParent();
				while (declStmt != null && !(declStmt instanceof Declaration)){
					declStmt = declStmt.getParent();
				}
				
				if (declStmt instanceof Declaration){
					int declIndex = declStmt.getParent().getChildren().indexOf(declStmt);
					declStmt.getParent().getChildren().add(declIndex, conditionals.get(i));
					conditionals.get(i).setParent(declStmt.getParent());
					
					
					// Adding the macro with an empty String..
					declIndex++;
					Opt optClone = (Opt) refactor.cloneNode(conditionals.get(i));
					optClone.setChildren(new ArrayList<Node>());
					
					DefineDirective define2 = new DefineDirective();
					define2.setName("ELEMS" + (i+1));
					StringLit emptyString = new StringLit();
					emptyString.setText("");
					
					define2.addChild(emptyString);
					emptyString.setParent(define2);
					
					optClone.addChild(define2);
					define2.setParent(optClone);
					
					optClone.setConditional(optClone.getConditional().not());
					
					declStmt.getParent().getChildren().add(declIndex, optClone);
					optClone.setParent(declStmt.getParent());
					
				}
			}
			
			
			/*refactor.removeConditionalsKeepingChildren(clone);
			
			int maxSize = 0;
			
			for (int i = 0; i < clone.getChildren().size(); i++){
				if (clone.getChildren().get(i) instanceof Initializer){
					maxSize++;
				}
			}
			
			Node initDeclarator = node.getParent();
			while (initDeclarator != null && !(initDeclarator instanceof InitDeclaratorI)){
				initDeclarator = initDeclarator.getParent();
			}
			
			if (initDeclarator != null){
				Node id = initDeclarator.getChildren().get(0).getChildren().get(0);
				if (id instanceof Id){
					
					Node declStmt = initDeclarator.getParent().getParent();
					
					while (declStmt != null && !(declStmt instanceof DeclarationStatement)){
						declStmt = declStmt.getParent();
					}
					
					/*if (!(declStmt instanceof DeclarationStatement)){
						declStmt = initDeclarator.getParent();
						while (declStmt != null && !(declStmt instanceof Declaration)){
							declStmt = declStmt.getParent();
						}
					}
					
					System.out.println(declStmt.getClass().getCanonicalName());*/
					
					/*if (declStmt instanceof DeclarationStatement /*|| declStmt instanceof Declaration*//*){
						
						// We need to get the real type..
						Node type = new IntSpecifier();
						
						if (declStmt.getChildren().get(0) instanceof Declaration){
							
							if (declStmt.getChildren().size() > 0){
								if (declStmt.getChildren().get(0).getChildren().size() > 0){
									if (declStmt.getChildren().get(0).getChildren().get(0).getChildren().size() > 0){
										if (declStmt.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().size() > 0){
											if (declStmt.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().get(0) instanceof Id){
												type = declStmt.getChildren().get(0).getChildren().get(0).getChildren().get(0).getChildren().get(0);
											}
										}
									}
								}
							}
							
						}
						
						
						// Array new declaration..
						Node decl = refactor.createArrayDeclarationStatement( ((Id)id).getName() , type, maxSize);
						
						// Initializing the array..
						int index = declStmt.getParent().getChildren().indexOf(declStmt);
						declStmt.getParent().getChildren().remove(declStmt);
						
						//if (declStmt.getChildren().get(0).getChildren().get(0).getChildren().get(1) instanceof StructDeclaration){
							// We need to add the struct declaration..
							
							//Node declClone = refactor.cloneNode(declStmt);
							//declClone.getChildren().get(0).getChildren().remove(1);
							//declClone.getChildren().get(0).accept(new VisitorPrinter(false));
							
							//System.out.println(declClone.getChildren().size());
							//declClone.getChildren().remove(1);
							//declStmt.getParent().getChildren().add((index), declClone);
							//index++;
						//}
						
						declStmt.getParent().getChildren().add(index, decl);
						decl.setParent(declStmt.getParent());
					
						
						
						// Initialize variable index..
						Constant c = new Constant();
						c.setValue("0");
						Node declIndex = refactor.createDeclarationStatement("index", new IntSpecifier(), c);
						
						index++;
						declStmt.getParent().getChildren().add(index, declIndex);
						declIndex.setParent(declStmt.getParent());
						
						for (int i = 0; i < node.getChildren().size(); i++){
							if (node.getChildren().get(i) instanceof Initializer){
								
								Node constant = node.getChildren().get(i).getChildren().get(0);
								Node exprStmt = refactor.createArrayExprStatement(((Id)id).getName(), "index++", constant);
								index++;
								declStmt.getParent().getChildren().add(index, exprStmt);
								exprStmt.setParent(declStmt.getParent());
							} else if (node.getChildren().get(i) instanceof Opt){
								Opt opt = (Opt) node.getChildren().get(i);
								Opt optClone = (Opt) refactor.cloneNode(opt);
								optClone.setChildren(new ArrayList<Node>());
								
								for (int j = 0; j < opt.getChildren().size(); j++){
									if (opt.getChildren().get(j) instanceof Initializer){
										Node constant = opt.getChildren().get(j).getChildren().get(0);
										Node exprStmt = refactor.createArrayExprStatement(((Id)id).getName(), "index++", constant);
										optClone.addChild(exprStmt);
									}
								}
								index++;
								declStmt.getParent().getChildren().add(index, optClone);
								optClone.setParent(declStmt.getParent());
							}
						}
					
					}
				}
			}*/
			
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(StringLit node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(ConditionalExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(DefineDirective node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(EnumSpecifier node) {
		VisitorCheckConditional conditionalChecker = new VisitorCheckConditional();
		node.accept(conditionalChecker);
		
		Refactor refactor = new Refactor();
		
		if (conditionalChecker.containConditional()){
			List<Opt> conditionals = refactor.getConditionalNodes(node);
			
			for (int i = 0; i < conditionals.size(); i++){
				DefineDirective define = new DefineDirective();
				define.setName("ELEMS" + (i+1));
				
				List<Node> children = conditionals.get(i).getChildren();
				for (int j = 0; j < children.size(); j++){
					define.addChild(children.get(j));
					children.get(j).setParent(define);
				}
				//Constant comma = new Constant();
				//comma.setValue(",");
				//define.addChild(comma);
				//comma.setParent(define);
				
				conditionals.get(i).setChildren(new ArrayList<Node>());
				
				
				// Adding the ELEMS macro in the array..
				int indexOpt = conditionals.get(i).getParent().getChildren().indexOf(conditionals.get(i));
				
				Constant constant = new Constant();
				constant.setValue("ELEMS" + (i+1));
			
				conditionals.get(i).getParent().getChildren().add(indexOpt, constant);
				constant.setParent(conditionals.get(i).getParent());
				
				conditionals.get(i).getParent().getChildren().remove((indexOpt+1));
				
				// Adding the #define directive..
				conditionals.get(i).addChild(define);
				define.setParent(conditionals.get(i));
				
				Node declStmt = node.getParent();
				while (declStmt != null && !(declStmt instanceof Declaration)){
					declStmt = declStmt.getParent();
				}
				
				if (declStmt instanceof Declaration){
					int declIndex = declStmt.getParent().getChildren().indexOf(declStmt);
					declStmt.getParent().getChildren().add(declIndex, conditionals.get(i));
					conditionals.get(i).setParent(declStmt.getParent());
					
					
					// Adding the macro with an empty String..
					declIndex++;
					Opt optClone = (Opt) refactor.cloneNode(conditionals.get(i));
					optClone.setChildren(new ArrayList<Node>());
					
					DefineDirective define2 = new DefineDirective();
					define2.setName("ELEMS" + (i+1));
					StringLit emptyString = new StringLit();
					emptyString.setText("");
					
					define2.addChild(emptyString);
					emptyString.setParent(define2);
					
					optClone.addChild(define2);
					define2.setParent(optClone);
					
					optClone.setConditional(optClone.getConditional().not());
					
					declStmt.getParent().getChildren().add(declIndex, optClone);
					optClone.setParent(declStmt.getParent());
					
				}
			}
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(Enumerator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
}
