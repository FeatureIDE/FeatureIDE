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

public class VisitorCheckIncompleteDirectives implements Visitor{

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
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Opt node) {
		
		if (!node.getConditional().isTautology()){
			System.out.println();
			if (node.getParent() instanceof CompoundStatement || node.getParent() instanceof TranslationUnit){
				System.out.print("Complete directive!!");
				node.accept(new VisitorPrinter(false));
			} else {
				System.out.print("Incomplete directive!!");
				node.accept(new VisitorPrinter(false));
			}
			
			for (int i = 0; i < node.getChildren().size(); i++){
				node.getChildren().get(i).accept(this);
			}
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
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(WhileStatement node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
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
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(ExprStatement node) {
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
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
	}

	@Override
	public void run(Declaration node) {
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
