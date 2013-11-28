package br.ufal.ic.colligens.refactoring.tree.visitor;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.RandomAccessFile;

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


public class VisitorPrinter implements Visitor{

	/*public VisitorPrinter() {
		
	}*/
	public VisitorPrinter(String filePath) throws FileNotFoundException {
		RandomAccessFile arq = new RandomAccessFile(filePath, "rw");
		try {
			arq.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		File file = new File(filePath);
		FileOutputStream fis = new FileOutputStream(file);
		PrintStream out = new PrintStream(fis);
		System.setOut(out);
	}
	
	public VisitorPrinter(boolean printToFile) {
		if (printToFile){
			File file = new File("output.c");  
			FileOutputStream fis;
			try {
				fis = new FileOutputStream(file);
				PrintStream out = new PrintStream(fis);  
				System.setOut(out);
			} catch (FileNotFoundException e) {
				e.printStackTrace();
			}  
		}
	}
	
	public void run(Choice node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (AtomicNamedDeclarator node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (ElifStatement node){
		System.out.print("else if ");
		for (int i = 0; i < node.getChildren().size(); i++){
			if (i == 1){
				if (node.getChildren().get(i) instanceof One){
					if (node.getChildren().get(i).getChildren().size() > 0){
						if (!(node.getChildren().get(i).getChildren().get(0) instanceof CompoundStatement)){
							System.out.println();
						}
					}
				}
			}node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (CompoundStatement node){
		System.out.println("{\n");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
		System.out.println("}");
		
	}

	public void run (DeclIdentifierList node){
		System.out.print("(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print(") ");
	}
	
	public void run (TranslationUnit node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (ExprList node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
			if (i < node.getChildren().size()-1){
				System.out.print(", ");
			}
		}
	}
	
	public void run (DeclParameterDeclList node){
		if (!(node.getParent() instanceof DefineDirective)){
			System.out.print("(");
		}
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
			if (i < node.getChildren().size()-1){
				System.out.print(", ");
			}
		}
		if (!(node.getParent() instanceof DefineDirective)){
			System.out.print(")");
		}
	}
	
	public void run (ParameterDeclarationD node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (StructDeclaration node){
		System.out.println("{");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println("}");
	}
	
	public void run (StructDeclarator node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println(";");
	}
	
	public void run (AtomicAbstractDeclarator node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (Pointer node){
		System.out.print("*");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (ParameterDeclarationAD node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (FunctionDef node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (Opt node){

		if (node.getChildren().size() > 0 && !node.getConditional().toString().trim().equals("False")){
			if (!node.getConditional().toString().trim().equals("True")){
				System.out.println("\n#if " + node.getConditional().toTextExpr().replace("definedEx", "defined"));
			}
			for (int i = 0; i < node.getChildren().size(); i++){
				node.getChildren().get(i).accept(this);
			}
			
			if (!node.getConditional().toString().trim().equals("True")){
				System.out.println("\n#endif\n");
			}
		}
	}
	
	public void run (Initializer node){
		Node parent = node.getParent();
		boolean arrayInit = false;
		while (parent != null){
			if (parent instanceof LcurlyInitializer){
				arrayInit = true;
				break;
			}
			parent = parent.getParent();
		}
		if (!arrayInit){
			if (!(node.getParent() instanceof DefineDirective)){
				System.out.print(" = ");
			}
		}
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		if (arrayInit){
			System.out.print(", ");
		}
	}
	
	public void run (InitDeclaratorI node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (TypeName node){
		System.out.print("(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print(") ");
	}
	
	public void run (One node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (Some node){
		if (node.getParent() instanceof IfStatement){
			System.out.print("else ");
		}
		
		if (node.getChildren().size() > 0){
			if (node.getChildren().get(0) instanceof One){
				if (node.getChildren().get(0).getChildren().size() > 0){
					if (!(node.getChildren().get(0).getChildren().get(0) instanceof CompoundStatement)){
						System.out.println();
					}
				}
			}
		}
			
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (SimplePostfixSuffix node){
		System.out.print("++");
	}
	
	public void run (PostfixExpr node){
		if (node.getParent().getParent() instanceof IfStatement){
			System.out.print("(");
		}
		
		// This code is for the FOR command.
		boolean hasParentFor = false;
		
		Node parent = node.getParent();
		while (parent != null){
			if (parent instanceof ForStatement){
				hasParentFor = true;
				break;
			}
			parent = parent.getParent();
		}
		
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		// Closing the for bracket.
		if (hasParentFor){
			System.out.print(")");
		}
		
		if (node.getParent().getParent() instanceof IfStatement){
			System.out.print(")");
		}
	}
	
	public void run (AssignExpr node){
		// This code avoids repeated (;)
		boolean hasParentStmt = false;
		
		Node parent = node.getParent();
		while (parent != null){
			if (parent instanceof ReturnStatement || parent instanceof ExprStatement){
				hasParentStmt = true;
				break;
			}
			parent = parent.getParent();
		}
				
		//boolean firstID = true;
		
		for (int i = 0; i < node.getChildren().size(); i++){
			/*if (node.getChildren().get(i) instanceof Id && firstID){
				System.out.print("=");
				firstID = false;
			}*/
			if (i == 1){
				System.out.print("=");
			}
			node.getChildren().get(i).accept(this);
		}
		
		if (!hasParentStmt){
			System.out.print("; ");
		}
	}
	
	public void run (IfStatement node){
		System.out.print("if ");
		
		for (int i = 0; i < node.getChildren().size(); i++){
			if (i == 1){
				if (node.getChildren().get(i) instanceof One){
					if (node.getChildren().get(i).getChildren().size() > 0){
						if (!(node.getChildren().get(i).getChildren().get(0) instanceof CompoundStatement)){
							System.out.println();
						}
					}
				}
			}
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (WhileStatement node){
		System.out.print("while ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (SizeOfExprT node){
		System.out.print("sizeof(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print(")");
	}
	
	public void run (SizeOfExprU node){
		System.out.print("sizeof ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (NestedNamedDeclarator node){
		System.out.print("(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
			if(node.getChildren().get(i) instanceof AtomicNamedDeclarator){
				System.out.print(")");
			}
		}
	}
	
	public void run (FunctionCall node){
		System.out.print("(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print(")");
	}
	
	public void run (ExprStatement node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println(";");
	}
	
	public void run (TypeDefTypeSpecifier node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (DeclArrayAccess node){
		System.out.print("[");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print("]");
	}
	
	public void run (ForStatement node){
		System.out.print("for(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (NAryExpr node){
		// Prints different in a for loop.
		boolean inAForStatement = false;
		
		Node parent = node.getParent();
		while (parent != null){
			if (parent instanceof ForStatement){
				inAForStatement = true;
				break;
			}
			parent = parent.getParent();
		}
		
		// Subexpressions do not need brackets.
		boolean inAnotherExpr = false;
		
		parent = node.getParent();
		while (parent != null){
			if (parent instanceof NAryExpr){
				inAnotherExpr = true;
				break;
			}
			parent = parent.getParent();
		}
		
		if (!inAForStatement && !inAnotherExpr){
			System.out.print("(");
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
		if (!inAForStatement && !inAnotherExpr){
			System.out.print(")");
		} else if (inAForStatement) {
			System.out.print("; ");
		}
	}
	
	public void run (NArySubExpr node){
		System.out.print(node.getOperator() + " ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (DoStatement node){
		System.out.print("do ");
		
		Node nAryExpr = null;
		
		for (int i = 0; i < node.getChildren().size(); i++){
			
			if (node.getChildren().get(i) instanceof NAryExpr){
				nAryExpr = node.getChildren().get(i);
			} else {
				node.getChildren().get(i).accept(this);
			}
		}
		
		System.out.print("while ");
		this.run( (NAryExpr) nAryExpr);
		System.out.println(";");
	}
	
	public void run (CaseStatement node){
		System.out.print("case ");
		for (int i = 0; i < node.getChildren().size(); i++){
			if (i == 1){
				System.out.println(":");
			}
			node.getChildren().get(i).accept(this);
			//if (node.getChildren().get(i) instanceof Constant){
				//System.out.println(":");
			//}
			
		}
	}
	
	public void run (SwitchStatement node){
		System.out.print("switch (");
		for (int i = 0; i < node.getChildren().size(); i++){
			if (i == 1){
				System.out.print(")");
			}
			node.getChildren().get(i).accept(this);
//			if (node.getChildren().get(i) instanceof Id){
//				System.out.print(")");
//			}
		}
		if (node.getParent() instanceof DefineDirective){
			System.out.print(")");
		}
	}
	
	public void run (DefaultStatement node){
		System.out.println("default:");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (DeclarationStatement node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println(";");
	}
	
	public void run (Declaration node){
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		if ( !(node.getParent() instanceof DeclarationStatement) && !(node.getParent() instanceof DefineDirective)){
			System.out.println(";");
		}
	}
	
	public void run (Constant node){
		System.out.print(node.getValue() + " ");
	}
	
	public void run (Id node){
		if (node.getParent().getParent() instanceof IfStatement){
			System.out.print("(");
		}
		
		System.out.print(node.getName() + " ");
		
		if (node.getParent().getParent() instanceof IfStatement){
			System.out.print(")");
		}
	}
	
	public void run (VoidSpecifier node){
		System.out.print("void ");
	}
	
	public void run (IntSpecifier node){
		System.out.print("int ");
	}
	
	public void run (DoubleSpecifier node){
		System.out.print("double ");
	}
	
	public void run (UnsignedSpecifier node){
		System.out.print("unsigned ");
	}
	
	public void run (VolatileSpecifier node){
		System.out.print("volatile ");
	}
	
	public void run (ConstSpecifier node){
		System.out.print("const ");
	}
	
	public void run (ExternSpecifier node){
		System.out.print("extern ");
	}
	
	public void run (TypedefSpecifier node){
		System.out.print("typedef ");
	}
	
	public void run (AutoSpecifier node){
		System.out.print("auto ");
	}
	
	public void run (BreakStatement node){
		System.out.println("break;");
	}
	
	public void run (CharSpecifier node){
		System.out.print("char ");
	}
	
	public void run (VarArgs node){
		System.out.print("... ");
	}
	
	public void run (PointerPostfixSuffix node){
		System.out.print(node.getType());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (PointerDerefExpr node){
		System.out.print("*");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (UnaryExpr node){
		System.out.print(node.getKind());
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	public void run (ContinueStatement node){
		System.out.println("continue;");
	}
	
	public void run (RegisterSpecifier node){
		System.out.print("register ");
	}
	
	public void run (StaticSpecifier node){
		System.out.print("static ");
	}
	
	public void run (FloatSpecifier node){
		System.out.print("float ");
	}
	
	public void run (ReturnStatement node){
		System.out.print("\nreturn ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println(";");
	}
	
	public void run (ShortSpecifier node){
		System.out.print("short ");
	}
	
	public void run (LongSpecifier node){
		System.out.print("long ");
	}
	
	public void run (StructOrUnionSpecifier node){
		System.out.print(node.getName() + " ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		
		/*boolean inAnotherStruct = false;
		
		Node parent = node.getParent();
		while (parent != null){
			if (parent instanceof StructDeclaration){
				inAnotherStruct = true;
				break;
			}
			parent = parent.getParent();
		}
		
		
		// For the special case of union or structure with the name at the end.
		
		boolean addCurlyBracket = false;
		
		for (int i = 0; i < node.getChildren().size(); i++){
			if (node.getChildren().get(i) instanceof Some){
				addCurlyBracket = true;
				break;
			}
			
		}
		
		if (!addCurlyBracket && !inAnotherStruct){
			System.out.println(node.getName() + " {");
		} else {
			System.out.print(node.getName() + " ");
		}
		
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
			if (node.getChildren().get(i) instanceof Some && !inAnotherStruct){
				System.out.println("{");
			}
			
		}
		if (!addCurlyBracket && !inAnotherStruct){
			System.out.print("} ");
		} else if (!inAnotherStruct){
			System.out.print("}");
		}*/
		
	}
	
	@Override
	public void run(PointerCreationExpr node) {
		System.out.print("&");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(UnaryOpExpr node) {
		System.out.print("(!(");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print("))");
	}
	
	@Override
	public void run(ArrayAccess node) {
		System.out.print("[");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print("]");
	}
	
	@Override
	public void run(LcurlyInitializer node) {
		System.out.print("{");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.print("}");
	}
	
	@Override
	public void run(StringLit node) {
		if (node.getChildren().size() == 0){
			if (node.getText().trim().equals("")){
				System.out.print("\"\"");
			} else {
				System.out.print(node.getText());
			}
		} else {
			for (int i = 0; i < node.getChildren().size(); i++){
				node.getChildren().get(i).accept(this);
			}
		}
	}
	
	@Override
	public void run(ConditionalExpr node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			if (i == 1){
				System.out.print("?");
			}
			if (i == 2){
				System.out.print(":");
			}
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(DefineDirective node) {
		System.out.print("#define " + node.getName() + " ");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
	}
	
	@Override
	public void run(EnumSpecifier node) {
		System.out.print("enum {");
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		System.out.println("}");
	}
	
	@Override
	public void run(Enumerator node) {
		for (int i = 0; i < node.getChildren().size(); i++){
			node.getChildren().get(i).accept(this);
		}
		if (!(node.getParent() instanceof DefineDirective)){
			System.out.print(", ");
		}
	}
}
