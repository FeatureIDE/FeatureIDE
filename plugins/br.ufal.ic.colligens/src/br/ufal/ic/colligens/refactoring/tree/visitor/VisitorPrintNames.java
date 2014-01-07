package br.ufal.ic.colligens.refactoring.tree.visitor;

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

public class VisitorPrintNames implements Visitor{

	@Override
	public void run(Choice node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}

	@Override
	public void run(AtomicNamedDeclarator node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ElifStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(CompoundStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclIdentifierList node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TranslationUnit node) {
		System.out.println(node.getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExprList node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclParameterDeclList node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ParameterDeclarationD node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructDeclaration node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructDeclarator node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AtomicAbstractDeclarator node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Pointer node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ParameterDeclarationAD node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(FunctionDef node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Opt node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName() + " : " + node.getConditional());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Initializer node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(InitDeclaratorI node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypeName node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(One node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Some node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SimplePostfixSuffix node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PostfixExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AssignExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(IfStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(WhileStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SizeOfExprT node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SizeOfExprU node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NestedNamedDeclarator node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(FunctionCall node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExprStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypeDefTypeSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclArrayAccess node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ForStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NAryExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(NArySubExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DoStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(CaseStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(SwitchStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DefaultStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DeclarationStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Declaration node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Constant node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Id node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VoidSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(IntSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(DoubleSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(UnsignedSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VolatileSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ConstSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExternSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(TypedefSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(AutoSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(BreakStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(CharSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(VarArgs node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PointerPostfixSuffix node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(PointerDerefExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(UnaryExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ContinueStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(RegisterSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StaticSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(FloatSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ReturnStatement node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ShortSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(LongSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(StructOrUnionSpecifier node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}
	
	@Override
	public void run(PointerCreationExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(UnaryOpExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(ArrayAccess node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(LcurlyInitializer node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}

	@Override
	public void run(StringLit node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(ConditionalExpr node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(DefineDirective node) {
		System.out.println(node.getClass().getCanonicalName() + " - " + node.getParent().getClass().getCanonicalName());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(EnumSpecifier node) {
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
