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
package de.ovgu.featureide.core.typecheck.check;

import java.util.List;
import java.util.Map;

import AST.ASTNode;
import AST.Block;
import AST.Expr;
import AST.ExprStmt;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.ReturnStmt;
import AST.Stmt;
import AST.VariableDeclaration;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.core.typecheck.parser.ClassTableEntry;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */
public class MethodCheck extends AbstractCheckPlugin {

    public MethodCheck() {
	plugin_name = "MethodCheck";
	registerNodeType(MethodAccess.class);
	registerNodeType(MethodDecl.class);
    }

    @Override
    public void invokeCheck(FeatureModel fm) {
	Map<Feature, List<MethodDecl>> methoddecl_map = getNodesByType(MethodDecl.class);

	for (Feature f : methoddecl_map.keySet()) {
	    System.out.println("Feature " + f.getName()
		    + " provides following methods: ");
	    for (MethodDecl md : methoddecl_map.get(f)) {
		System.out.println("\t" + md.hostType().name() + "@"
			+ md.signature());
	    }
	}

	Map<Feature, List<MethodAccess>> methodaccess_map = getNodesByType(MethodAccess.class);
	for (Feature f : methodaccess_map.keySet()) {
	    System.out.println("Feature " + f.getName()
		    + " needs following methods: ");
	    for (MethodAccess ma : methodaccess_map.get(f)) {
		if (ma.decl().hostType().name().equals("Unknown")) {
		    System.out.println(ma);
		    for (Expr e : ma.getArgs()) {
			System.out.println(e.type().name());
		    }
		} else {
		    // System.out.println("\t" + ma.decl().hostType().name() +
		    // "@"
		    // + ma.decl().signature());
		}
	    }
	}
    }
}
