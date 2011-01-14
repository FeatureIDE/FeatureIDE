package de.ovgu.featureide.core.featurehouse.FSTParser;

import java.io.File;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import de.ovgu.cide.fstgen.ast.FSTNode;
import de.ovgu.cide.fstgen.ast.FSTNonTerminal;
import de.ovgu.cide.fstgen.ast.FSTTerminal;

import de.ovgu.featureide.core.featurehouse.model.java.Class;

/**
 * Parses a feature house java file.
 * 
 * @author Dariusz Krolikowski
 */
public class FSTParser {

	private HashMap<String, List<JavaToken>> fileList = new HashMap<String, List<JavaToken>>();
	
	private String getArguments(String body){
		int start = body.indexOf("(");
		int end = body.indexOf(")");
		
		return body.substring(start+1, end);
	}
	
	
	private JavaToken setModifier(JavaToken token, String modifier){
		
		token.setType(modifier.substring(modifier.lastIndexOf(" ")+1));

		if (modifier.contains("abstract"))
			token.set_abstract(true);
		if (modifier.contains("final"))
			token.set_final(true);
		if (modifier.contains("native"))
			token.set_native(true);
		if (modifier.contains("private"))
			token.set_private(true);
		if (modifier.contains("protected"))
			token.set_protected(true);
		if (modifier.contains("public"))
			token.set_public(true);
		if (modifier.contains("strictfp"))
			token.set_strictfp(true);
		if (modifier.contains("static"))
			token.set_static(true);
		if (modifier.contains("synchronized"))
			token.set_synchronized(true);
		if (modifier.contains("transient"))
			token.set_transient(true);
		if (modifier.contains("volatile"))
			token.set_volatile(true);
		
		return token;
	}
		
	public FSTParser(List<FSTNode> nodes ){

		List<JavaToken> tokenList = new LinkedList<JavaToken>();

		String file = "";					// for the "old" parser
		Class javaClass = new Class("");	// for featureIDE fst
		
		for (FSTNode node : nodes) {
			
			if (node.getType().equals("Feature")){
				tokenList = new LinkedList<JavaToken>();
			}
			else if (node.getType().equals("EOF Marker")){
				
				// System.out.println(node.getName());
				// node.getName() equals the absolute file path
	
				file = node.getName().substring(node.getName().lastIndexOf(File.separator)+1);
				javaClass.setName(file);	// TODO: with or without dot for fst? 
			}
			else if (node.getType().equals("ClassDeclaration")){
				if(node instanceof FSTNonTerminal){
					FSTNonTerminal nonterminal = (FSTNonTerminal) node;

					for (FSTNode child : nonterminal.getChildren()){
						if(child instanceof FSTTerminal){
							FSTTerminal terminal = (FSTTerminal) child;
							JavaToken token;
							
							if (terminal.getType().equals("FieldDecl")){
								// field declaration
								token =  new JavaToken(terminal.getName(), "", true);
								token = setModifier(token, terminal.getBody().substring(0,terminal.getBody().indexOf(terminal.getName())-1));
								tokenList.add(token);
								// TODO: javaClass.addField(key, field) ?
							}
							else if (terminal.getType().equals("MethodDecl")){
								// method declaration
								String name = terminal.getName().substring(0,terminal.getName().indexOf("("));
								token =  new JavaToken(name, getArguments(terminal.getBody()), false);
								token = setModifier(token, terminal.getBody().substring(0,terminal.getBody().indexOf(name)-1));
								tokenList.add(token);
								// TODO: javaClass.addMethod(key, method) ?
							}
							else if (terminal.getType().equals("ConstructorDecl")){
								// constructor declaration
							}
						}
					}
				}
			}
			else if (node.getType().equals("CompilationUnit")){
				// this means, the current file/class is parsed
				fileList.put(file, tokenList);
			}
		}
	}

	/**
	 * @return the fileList
	 */
	public HashMap<String, List<JavaToken>> getFileList() {
		return fileList;
	}


}
