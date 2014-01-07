package br.ufal.ic.colligens.refactoring.core;

import br.ufal.ic.colligens.refactoring.tree.AssignExpr;
import br.ufal.ic.colligens.refactoring.tree.AtomicAbstractDeclarator;
import br.ufal.ic.colligens.refactoring.tree.AtomicNamedDeclarator;
import br.ufal.ic.colligens.refactoring.tree.AutoSpecifier;
import br.ufal.ic.colligens.refactoring.tree.BreakStatement;
import br.ufal.ic.colligens.refactoring.tree.CaseStatement;
import br.ufal.ic.colligens.refactoring.tree.CharSpecifier;
import br.ufal.ic.colligens.refactoring.tree.CompoundStatement;
import br.ufal.ic.colligens.refactoring.tree.ConstSpecifier;
import br.ufal.ic.colligens.refactoring.tree.Constant;
import br.ufal.ic.colligens.refactoring.tree.ContinueStatement;
import br.ufal.ic.colligens.refactoring.tree.DeclArrayAccess;
import br.ufal.ic.colligens.refactoring.tree.DeclIdentifierList;
import br.ufal.ic.colligens.refactoring.tree.DeclParameterDeclList;
import br.ufal.ic.colligens.refactoring.tree.Declaration;
import br.ufal.ic.colligens.refactoring.tree.DeclarationStatement;
import br.ufal.ic.colligens.refactoring.tree.DefaultStatement;
import br.ufal.ic.colligens.refactoring.tree.DoStatement;
import br.ufal.ic.colligens.refactoring.tree.DoubleSpecifier;
import br.ufal.ic.colligens.refactoring.tree.ElifStatement;
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
import br.ufal.ic.colligens.refactoring.tree.LongSpecifier;
import br.ufal.ic.colligens.refactoring.tree.NAryExpr;
import br.ufal.ic.colligens.refactoring.tree.NArySubExpr;
import br.ufal.ic.colligens.refactoring.tree.NestedNamedDeclarator;
import br.ufal.ic.colligens.refactoring.tree.Node;
import br.ufal.ic.colligens.refactoring.tree.ParameterDeclarationAD;
import br.ufal.ic.colligens.refactoring.tree.ParameterDeclarationD;
import br.ufal.ic.colligens.refactoring.tree.Pointer;
import br.ufal.ic.colligens.refactoring.tree.PointerDerefExpr;
import br.ufal.ic.colligens.refactoring.tree.PointerPostfixSuffix;
import br.ufal.ic.colligens.refactoring.tree.PostfixExpr;
import br.ufal.ic.colligens.refactoring.tree.RegisterSpecifier;
import br.ufal.ic.colligens.refactoring.tree.ReturnStatement;
import br.ufal.ic.colligens.refactoring.tree.ShortSpecifier;
import br.ufal.ic.colligens.refactoring.tree.SimplePostfixSuffix;
import br.ufal.ic.colligens.refactoring.tree.SizeOfExprT;
import br.ufal.ic.colligens.refactoring.tree.SizeOfExprU;
import br.ufal.ic.colligens.refactoring.tree.StaticSpecifier;
import br.ufal.ic.colligens.refactoring.tree.StringLit;
import br.ufal.ic.colligens.refactoring.tree.StructDeclaration;
import br.ufal.ic.colligens.refactoring.tree.StructDeclarator;
import br.ufal.ic.colligens.refactoring.tree.StructOrUnionSpecifier;
import br.ufal.ic.colligens.refactoring.tree.SwitchStatement;
import br.ufal.ic.colligens.refactoring.tree.TypeDefTypeSpecifier;
import br.ufal.ic.colligens.refactoring.tree.TypeName;
import br.ufal.ic.colligens.refactoring.tree.TypedefSpecifier;
import br.ufal.ic.colligens.refactoring.tree.UnaryExpr;
import br.ufal.ic.colligens.refactoring.tree.UnsignedSpecifier;
import br.ufal.ic.colligens.refactoring.tree.VarArgs;
import br.ufal.ic.colligens.refactoring.tree.VolatileSpecifier;
import br.ufal.ic.colligens.refactoring.tree.WhileStatement;
import scala.Product;
import scala.Some;
import de.fosd.typechef.conditional.Choice;
import de.fosd.typechef.conditional.One;
import de.fosd.typechef.conditional.Opt;
import de.fosd.typechef.parser.c.ArrayAccess;
import de.fosd.typechef.parser.c.ConditionalExpr;
import de.fosd.typechef.parser.c.LcurlyInitializer;
import de.fosd.typechef.parser.c.UnaryOpExpr;
import de.fosd.typechef.parser.c.VoidSpecifier;

public class GenerateAST {

	// This method receives the translation units from TypeChef and my Translation Unit (tree.TranslationUnit).
	public void generate(Product node, Node parent){
		for (int i = 0; i < node.productArity(); i++){
			if (node.productElement(i) instanceof Product){
				Node myNode = this.getNode( (Product) node.productElement(i));
				if (myNode != null && parent != null){
					myNode.setParent(parent);
					parent.addChild(myNode);
					this.generate( (Product) node.productElement(i), myNode);
				} else {
					this.generate( (Product) node.productElement(i), parent);
				}		
			} 
		}
		
	}
	
	@SuppressWarnings("rawtypes")
	public Node getNode(Product node){
		
		if (node instanceof de.fosd.typechef.parser.c.CompoundStatement){
			return new CompoundStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.FunctionDef){
			return new FunctionDef();
		} else if (node instanceof de.fosd.typechef.parser.c.Id){
			Id id = new Id(); 
			id.setName(((de.fosd.typechef.parser.c.Id) node).name());
			return id;
		} else if (node instanceof de.fosd.typechef.parser.c.AtomicNamedDeclarator){
			return new AtomicNamedDeclarator();
		} else if (node instanceof Opt<?>){
			br.ufal.ic.colligens.refactoring.tree.Opt opt = new br.ufal.ic.colligens.refactoring.tree.Opt();
			opt.setConditional( ( (Opt) node).feature() );
			return opt;
		} else if (node instanceof VoidSpecifier){
			return new br.ufal.ic.colligens.refactoring.tree.VoidSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.DeclIdentifierList){
			return new DeclIdentifierList();
		} else if (node instanceof de.fosd.typechef.parser.c.IntSpecifier){
			return new IntSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.DoubleSpecifier){
			return new DoubleSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.UnsignedSpecifier){
			return new UnsignedSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.VolatileSpecifier){
			return new VolatileSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.ConstSpecifier){
			return new ConstSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.ExternSpecifier){
			return new ExternSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.DeclarationStatement){
			return new DeclarationStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.Declaration){
			return new Declaration();
		} else if (node instanceof de.fosd.typechef.parser.c.InitDeclaratorI){
			return new InitDeclaratorI();
		} else if (node instanceof de.fosd.typechef.parser.c.Initializer){
			return new Initializer();
		} else if (node instanceof de.fosd.typechef.parser.c.Constant){
			Constant constant = new Constant(); 
			constant.setValue(((de.fosd.typechef.parser.c.Constant) node).value());
			return constant;
		} else if (node instanceof de.fosd.typechef.parser.c.IfStatement){
			return new IfStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.NAryExpr){
			return new NAryExpr();
		} else if (node instanceof de.fosd.typechef.parser.c.NArySubExpr){
			NArySubExpr nArySubExpr = new NArySubExpr();
			nArySubExpr.setOperator( ((de.fosd.typechef.parser.c.NArySubExpr) node).op() );
			return nArySubExpr;
		} else if (node instanceof de.fosd.typechef.parser.c.WhileStatement){
			return new WhileStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.ForStatement){
			return new ForStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.AssignExpr){
			return new AssignExpr();
		} else if (node instanceof de.fosd.typechef.parser.c.PostfixExpr){
			return new PostfixExpr();
		} else if (node instanceof de.fosd.typechef.parser.c.SimplePostfixSuffix){
			return new SimplePostfixSuffix();
		} else if (node instanceof de.fosd.typechef.parser.c.TypedefSpecifier){
			return new TypedefSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.AutoSpecifier){
			return new AutoSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.BreakStatement){
			return new BreakStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.CharSpecifier){
			return new CharSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.ContinueStatement){
			return new ContinueStatement();
		} else if (node instanceof One<?>){
			return new br.ufal.ic.colligens.refactoring.tree.One();
		} else if (node instanceof Some<?>){
			return new br.ufal.ic.colligens.refactoring.tree.Some();
		} else if (node instanceof de.fosd.typechef.parser.c.ElifStatement){
			return new ElifStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.RegisterSpecifier){
			return new RegisterSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.StaticSpecifier){
			return new StaticSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.ReturnStatement){
			return new ReturnStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.ShortSpecifier){
			return new ShortSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.StructOrUnionSpecifier){
			StructOrUnionSpecifier s = new StructOrUnionSpecifier();
			if ( ((de.fosd.typechef.parser.c.StructOrUnionSpecifier)node).isUnion() ){
				s.setName("union");
			} else {
				s.setName("struct");
			}
			return s;
		} else if (node instanceof de.fosd.typechef.parser.c.CaseStatement){
			return new CaseStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.DefaultStatement){
			return new DefaultStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.LongSpecifier){
			return new LongSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.SwitchStatement){
			return new SwitchStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.DoStatement){
			return new DoStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.ExprStatement){
			return new ExprStatement();
		} else if (node instanceof de.fosd.typechef.parser.c.TypeDefTypeSpecifier){
			return new TypeDefTypeSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.SizeOfExprT){
			return new SizeOfExprT();
		} else if (node instanceof de.fosd.typechef.parser.c.SizeOfExprU){
			return new SizeOfExprU();
		} else if (node instanceof de.fosd.typechef.parser.c.FunctionCall){
			return new FunctionCall();
		} else if (node instanceof de.fosd.typechef.parser.c.ExprList){
			return new ExprList();
		} else if (node instanceof de.fosd.typechef.parser.c.DeclParameterDeclList){
			return new DeclParameterDeclList();
		} else if (node instanceof de.fosd.typechef.parser.c.ParameterDeclarationD){
			return new ParameterDeclarationD();
		} else if (node instanceof de.fosd.typechef.parser.c.ParameterDeclarationAD){
			return new ParameterDeclarationAD();
		} else if (node instanceof de.fosd.typechef.parser.c.AtomicAbstractDeclarator){
			return new AtomicAbstractDeclarator();
		} else if (node instanceof de.fosd.typechef.parser.c.Pointer){
			return new Pointer();
		} else if (node instanceof de.fosd.typechef.parser.c.StructDeclaration){
			return new StructDeclaration();
		} else if (node instanceof de.fosd.typechef.parser.c.StructDeclarator){
			return new StructDeclarator();
		} else if (node instanceof de.fosd.typechef.parser.c.DeclArrayAccess){
			return new DeclArrayAccess();
		} else if (node instanceof de.fosd.typechef.parser.c.NestedNamedDeclarator){
			return new NestedNamedDeclarator();
		} else if (node instanceof de.fosd.typechef.parser.c.FloatSpecifier){
			return new FloatSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.VarArgs){
			return new VarArgs();
		} else if (node instanceof de.fosd.typechef.parser.c.PointerPostfixSuffix){
			de.fosd.typechef.parser.c.PointerPostfixSuffix p = (de.fosd.typechef.parser.c.PointerPostfixSuffix) node;
			
			PointerPostfixSuffix myP = new PointerPostfixSuffix();
			myP.setType(p.kind());
			
			return myP;
		} else if (node instanceof de.fosd.typechef.parser.c.UnaryExpr){
			UnaryExpr u = new UnaryExpr();
			u.setKind(((de.fosd.typechef.parser.c.UnaryExpr) node).kind());
			return u;
		} else if (node instanceof de.fosd.typechef.parser.c.TypeName){
			return new TypeName();
		} else if (node instanceof de.fosd.typechef.parser.c.PointerDerefExpr){
			return new PointerDerefExpr();
		} else if (node instanceof Choice<?>){
			return new br.ufal.ic.colligens.refactoring.tree.Choice();
		} else if (node instanceof de.fosd.typechef.parser.c.PointerCreationExpr){
			return new br.ufal.ic.colligens.refactoring.tree.PointerCreationExpr();
		} else if (node instanceof ArrayAccess){
			return new br.ufal.ic.colligens.refactoring.tree.ArrayAccess();
		} else if (node instanceof de.fosd.typechef.parser.c.EnumSpecifier){
			return new br.ufal.ic.colligens.refactoring.tree.EnumSpecifier();
		} else if (node instanceof de.fosd.typechef.parser.c.Enumerator){
			return new br.ufal.ic.colligens.refactoring.tree.Enumerator();
		} else if (node instanceof UnaryOpExpr){
			return new br.ufal.ic.colligens.refactoring.tree.UnaryOpExpr();
		} else if (node instanceof LcurlyInitializer){
			return new br.ufal.ic.colligens.refactoring.tree.LcurlyInitializer();
		} else if (node instanceof de.fosd.typechef.parser.c.StringLit){
			StringLit mainStringLit = new StringLit();
			
			try {
				//First Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)   ((Product) node.productElement(0)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			try {
				//Second Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)   ((Product)((Product) node.productElement(0)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			try {
				//Third Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)  ((Product)((Product)((Product) node.productElement(0)).productElement(1)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			try {
				//Fourth Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)    ((Product)((Product)((Product)((Product) node.productElement(0)).productElement(1)).productElement(1)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			try {
				//Fifth Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)    ((Product)((Product)((Product)((Product)((Product) node.productElement(0)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			
			try {
				//Sixth Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)   ((Product)((Product)((Product)((Product)((Product)((Product) node.productElement(0)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			try {
				//Seventh Opt
				StringLit lit = new StringLit();
				Opt<?> opt = (Opt<?>)   ((Product)((Product)((Product)((Product)((Product)((Product)((Product) node.productElement(0)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(1)).productElement(0);
				lit.setText(  opt.productElement(1).toString()   );
				
				br.ufal.ic.colligens.refactoring.tree.Opt opt1 = new br.ufal.ic.colligens.refactoring.tree.Opt();
				opt1.setConditional(opt.feature());
				opt1.addChild(lit);
				lit.setParent(opt1);
				
				mainStringLit.addChild(opt1);
				opt1.setParent(mainStringLit);
			} catch (Exception e) {
				// Do nothing..
			}
			
			
			return mainStringLit;
		} else if (node instanceof ConditionalExpr){
			return new br.ufal.ic.colligens.refactoring.tree.ConditionalExpr();
		}
		
		
		return null;
	}
	
}
