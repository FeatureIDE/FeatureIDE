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

public interface Visitor {

	public void run (Choice node);
	
	public void run (AtomicNamedDeclarator node);
	
	public void run (ElifStatement node);
	
	public void run (CompoundStatement node);

	public void run (DeclIdentifierList node);
	
	public void run (TranslationUnit node);
	
	public void run (ExprList node);
	
	public void run (DeclParameterDeclList node);
	
	public void run (ParameterDeclarationD node);
	
	public void run (StructDeclaration node);
	
	public void run (StructDeclarator node);
	
	public void run (AtomicAbstractDeclarator node);
	
	public void run (Pointer node);
	
	public void run (ParameterDeclarationAD node);
	
	public void run (FunctionDef node);
	
	public void run (Opt node);
	
	public void run (Initializer node);
	
	public void run (InitDeclaratorI node);
	
	public void run (TypeName node);
	
	public void run (One node);
	
	public void run (Some node);
	
	public void run (SimplePostfixSuffix node);
	
	public void run (PostfixExpr node);
	
	public void run (AssignExpr node);
	
	public void run (IfStatement node);
	
	public void run (WhileStatement node);
	
	public void run (SizeOfExprT node);
	
	public void run (SizeOfExprU node);
	
	public void run (NestedNamedDeclarator node);
	
	public void run (FunctionCall node);
	
	public void run (ExprStatement node);
	
	public void run (TypeDefTypeSpecifier node);
	
	public void run (DeclArrayAccess node);
	
	public void run (ForStatement node);
	
	public void run (NAryExpr node);
	
	public void run (NArySubExpr node);
	
	public void run (DoStatement node);
	
	public void run (CaseStatement node);
	
	public void run (SwitchStatement node);
	
	public void run (DefaultStatement node);
	
	public void run (DeclarationStatement node);
	
	public void run (Declaration node);
	
	public void run (Constant node);
	
	public void run (Id node);
	
	public void run (VoidSpecifier node);
	
	public void run (IntSpecifier node);
	
	public void run (DoubleSpecifier node);
	
	public void run (UnsignedSpecifier node);
	
	public void run (VolatileSpecifier node);
	
	public void run (ConstSpecifier node);
	
	public void run (ExternSpecifier node);
	
	public void run (TypedefSpecifier node);
	
	public void run (AutoSpecifier node);
	
	public void run (BreakStatement node);
	
	public void run (CharSpecifier node);
	
	public void run (VarArgs node);
	
	public void run (PointerPostfixSuffix node);
	
	public void run (PointerDerefExpr node);
	
	public void run (UnaryExpr node);
	
	public void run (ContinueStatement node);
	
	public void run (RegisterSpecifier node);
	
	public void run (StaticSpecifier node);
	
	public void run (FloatSpecifier node);
	
	public void run (ReturnStatement node);
	
	public void run (ShortSpecifier node);
	
	public void run (LongSpecifier node);
	
	public void run (StructOrUnionSpecifier node);
	
	public void run (PointerCreationExpr node);
	
	public void run (UnaryOpExpr node);
	
	public void run (ArrayAccess node);
	
	public void run (LcurlyInitializer node);
	
	public void run (StringLit node);
	
	public void run (ConditionalExpr node);
	
	public void run (DefineDirective node);
	
	public void run (EnumSpecifier node);
	
	public void run (Enumerator node);
	
}
