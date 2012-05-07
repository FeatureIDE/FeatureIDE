/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.core.typecheck.parser;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.commons.cli.ParseException;

import AST.ASTNode;
import AST.ClassDecl;
import AST.CompilationUnit;
import AST.IntrosRefsUtil;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.Program;
import AST.ReferenceType;
import AST.TypeAccess;
import fuji.CompilerWarningException;
import fuji.Composition;
import fuji.FeatureDirNotFoundException;
import fuji.Main;
import fuji.SemanticErrorException;
import fuji.SyntacticErrorException;
import fuji.WrongArgumentException;

/**
 * 
 * @author Sönke Holthusen
 * 
 */
public class FujiWrapper {
    
    
    
    public static void getIntros(CompilationUnit cu,
	    java.util.List<String> featureModulePathnames) {
	java.util.Collection<ReferenceType> refiningTypes = cu
		.getRefiningTypes();
	if (refiningTypes != null) {
	    for (ReferenceType rt : refiningTypes) {
		System.out.print(IntrosRefsUtil.introPrefix(rt,
			featureModulePathnames));
		System.out.println(IntrosRefsUtil.typeDeclQName(rt));
	    }
	}
	for (int i = 0; i < cu.getNumChild(); i++) {
	    cu.getChild(i).printIntros(featureModulePathnames);
	}

    }

    public static boolean hasSuperClass(ClassDecl cl, ClassDecl superclass) {
	if (cl.hasSuperclass()) {
	    if (cl.superclass().equals(superclass)) {
		return true;
	    } else {
		return hasSuperClass(cl.superclass(), superclass);
	    }
	}
	return false;
    }

    public static Iterator<Program> getFujiCompositionIterator(
	    List<String> features, String feature_path)
	    throws WrongArgumentException, ParseException, IOException,
	    FeatureDirNotFoundException, SyntacticErrorException,
	    SemanticErrorException, CompilerWarningException {
	String[] fuji_options = { "-progmode", "-basedir", feature_path };

	Main m = new Main(fuji_options, features);

	Composition composition = m.getComposition(m);

	return composition.getASTIterator();
    }

    public static ArrayList<ASTNode> getMethodAccesses(ASTNode method) {
	ArrayList<ASTNode> method_accesses = new ArrayList<ASTNode>();
	for (int i = method.getNumChild(); i > 0; i--) {
	    ASTNode node = method.getChild(i - 1);

	    if (node instanceof MethodAccess) {
		method_accesses.add(node);
	    }

	    method_accesses.addAll(getMethodAccesses(node));
	}
	return method_accesses;
    }

    public static ArrayList<ASTNode> getTypeAccesses(ASTNode method) {
	ArrayList<ASTNode> type_accesses = new ArrayList<ASTNode>();
	for (int i = method.getNumChild(); i > 0; i--) {
	    ASTNode node = method.getChild(i - 1);

	    if (node instanceof TypeAccess) {
		type_accesses.add(node);
	    }

	    type_accesses.addAll(getTypeAccesses(node));
	}
	return type_accesses;
    }
    
    public static List<MethodDecl> getMethodDecls(ASTNode node){
	List<MethodDecl> methods = new ArrayList<MethodDecl>();
	for(int i = 0; i < node.getNumChild(); i++){
	    ASTNode child = node.getChild(i);
	    if(child instanceof MethodDecl){
		methods.add((MethodDecl) child);
	    }
	    methods.addAll(getMethodDecls(child));
	}
	return methods;
    }

}
