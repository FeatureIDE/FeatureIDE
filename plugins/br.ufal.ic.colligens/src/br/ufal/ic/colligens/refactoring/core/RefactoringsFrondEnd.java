package br.ufal.ic.colligens.refactoring.core;

import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import scala.Product;
import br.ufal.ic.colligens.models.FileProxy;
import br.ufal.ic.colligens.models.RenderParserError;
import br.ufal.ic.colligens.refactoring.tree.TranslationUnit;
import br.ufal.ic.colligens.refactoring.tree.visitor.VisitorAntiPatterns;
import br.ufal.ic.colligens.refactoring.tree.visitor.VisitorOrganizeMyAST;
import br.ufal.ic.colligens.refactoring.tree.visitor.VisitorPrinter;
import de.fosd.typechef.lexer.LexerException;
import de.fosd.typechef.lexer.options.OptionException;
import de.fosd.typechef.parser.c.AST;
import de.fosd.typechef.parser.c.AtomicNamedDeclarator;
import de.fosd.typechef.parser.c.CParser;
import de.fosd.typechef.parser.c.FunctionDef;
import de.fosd.typechef.parser.c.ParserMain;
import de.fosd.typechef.parser.c.ParserOptions;

public class RefactoringsFrondEnd {

	public void findMethodNames(Product node) {
		scala.collection.Iterator<Object> children = node.productIterator();

		Object child = null;
		while (children.hasNext()) {
			child = children.next();
			if (child instanceof AtomicNamedDeclarator) {
				if (node instanceof FunctionDef) {
					System.out.println(child);
				}
			}
			if (child instanceof Product) {
				this.findMethodNames((Product) child);
			}
		}
	}

	public void refactoringFile(FileProxy fileProxy) throws IOException,
			LexerException, OptionException {
		ParserOptions myParserOptions = new MyParserOptions();

		((RenderParserError) myParserOptions.renderParserError())
				.setFile(fileProxy);

		ParserMain parser = new ParserMain(new CParser(null, false));

		List<String> includes = new ArrayList<String>();

		// FASTER
		AST ast = parser.parserMain(fileProxy.getFileToAnalyse(), includes,
				myParserOptions);

		br.ufal.ic.colligens.refactoring.tree.Node myAst = new TranslationUnit();
		// t.generateMyAST(ast, myAst);

		new GenerateAST().generate(ast, myAst);

		myAst.accept(new VisitorOrganizeMyAST());

		VisitorAntiPatterns visitorAntiPatterns = new VisitorAntiPatterns();

		myAst.accept(visitorAntiPatterns);

		// if (Refactor.isEmpty()) {
		// return null;
		// }

		myAst.accept(new VisitorOrganizeMyAST());

		String filePathOut = System.getProperty("java.io.tmpdir") + "/"
				+ myAst.hashCode() + ".c";

		PrintStream out = System.out;

		myAst.accept(new VisitorPrinter(filePathOut));

		System.setOut(out);

		new OrganizeCode().organize(filePathOut);

		fileProxy.setFileToAnalyse(filePathOut);

	}
}
