package br.ufal.ic.colligens.controllers;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.TextSelection;

import tree.Node;
import tree.visitor.VisitorPrinter;
import br.ufal.ic.colligens.activator.Colligens;
import br.ufal.ic.colligens.controllers.core.PluginException;
import br.ufal.ic.colligens.models.PlatformException;
import br.ufal.ic.colligens.models.PlatformHeader;
import core.GeneralFrontend;
import core.RefactoringFrontend;
import core.presence.condition.PresenceConditionVisitor;
import de.fosd.typechef.lexer.options.OptionException;

public class PresenceConditionController {
	private final TextSelection selection;
	private IFile file = null;
	private final int line;
	private final String code;
	private Collection<Node> nodes;
	public static final String MARKER_TYPE = Colligens.PLUGIN_ID
			+ ".presencecondition";

	public PresenceConditionController(TextSelection selection, IFile file,
			int line, String code) {
		this.selection = selection;
		this.file = file;
		this.line = line;
		this.code = code;
	}

	public void run() throws PluginException, OptionException {
		PlatformHeader platformHeader = new PlatformHeader();
		try {
			platformHeader.setProject(file.getProject().getName());
			platformHeader.stubs();
		} catch (PlatformException e) {
			e.printStackTrace();
			throw new PluginException("");
		}

		tree.Node ast = GeneralFrontend.getAST(file.getLocation().toString(),
				platformHeader.stubsAbsolutePath());

		nodes = new LinkedList<Node>();

		ast.accept(new PresenceConditionVisitor());

		this.presenceCondition(ast);

		System.out.println("----\n\n");
	}

	private void presenceCondition(Node node) {
		if (node.getPositionFrom() != null
				&& (node.getPositionFrom().getLine() >= line - 5 && node
						.getPositionFrom().getLine() <= line + 5)) {
			PrintStream out = System.out;
			node.accept(new VisitorPrinter(true));
			System.setOut(out);
			try {
				Runtime.getRuntime().exec(
						"/usr/bin/uncrustify -o "
								+ RefactoringFrontend.outputFilePath
								+ " -c default.cfg -f "
								+ RefactoringFrontend.outputFilePath);
			} catch (IOException e) {
				e.printStackTrace();
			}

			try {
				String codeNode = readFile(RefactoringFrontend.outputFilePath)
						.trim();
				if (codeNode.contains(code.trim())) {
					System.out.println("Presence Condition: "
							+ node.getPresenceCondition() + ", from line "
							+ line + "." + node.getPositionFrom().getLine());
					node.accept(new VisitorPrinter(false));
					System.out.println("\n\n");

					IMarker marker;
					try {
						marker = file.createMarker(MARKER_TYPE);

						marker.setAttribute(
								IMarker.MESSAGE,
								"Presence Condition: "
										+ node.getPresenceCondition());
						marker.setAttribute(IMarker.SEVERITY,
								IMarker.SEVERITY_INFO);
						marker.setAttribute(IMarker.LINE_NUMBER, line);
					} catch (CoreException e) {
						e.printStackTrace();
					}
					nodes.add(node);
				}
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		for (Node child : node.getChildren()) {
			this.presenceCondition(child);
		}
	}

	public Collection<Node> getNodes() {
		if (nodes.isEmpty())
			return null;

		for (Iterator node = nodes.iterator(); node.hasNext();) {
			Node type = (Node) node.next();

		}

		return nodes;
	}

	private String readFile(String fileName) throws IOException {
		BufferedReader br = new BufferedReader(new FileReader(fileName));
		try {
			StringBuilder sb = new StringBuilder();
			String line = br.readLine();

			while (line != null) {
				sb.append(line);
				sb.append("\n");
				line = br.readLine();
			}
			return sb.toString();
		} finally {
			br.close();
		}
	}
}
