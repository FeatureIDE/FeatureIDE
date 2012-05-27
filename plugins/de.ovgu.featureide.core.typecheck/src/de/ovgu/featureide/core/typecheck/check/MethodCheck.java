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

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import AST.ASTNode;
import AST.Access;
import AST.Block;
import AST.CompilationUnit;
import AST.Expr;
import AST.ExprStmt;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.ReturnStmt;
import AST.Stmt;
import AST.UnknownType;
import AST.VarAccess;
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
	plugin_name = "MethodAccess Check";
	registerNodeType(MethodAccess.class);
	registerNodeType(MethodDecl.class);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.ovgu.featureide.core.typecheck.check.ICheckPlugin#init()
     */
    @Override
    public void init() {
	// TODO Auto-generated method stub

    }

    @Override
    public void invokeCheck(FeatureModel fm) {
	Map<Feature, List<MethodDecl>> methoddecl_map = getNodesByType(MethodDecl.class);
	Map<Feature, List<MethodAccess>> methodaccess_map = getNodesByType(MethodAccess.class);

	for (Feature f : methodaccess_map.keySet()) {
	    for (MethodAccess ma : methodaccess_map.get(f)) {
		Method m = new Method(ma);
		// if (!m.isAnonymous())
		// System.out.println(m);
	    }
	}

	// for (Feature f : methoddecl_map.keySet()) {
	// for (MethodDecl md : methoddecl_map.get(f)) {
	// Method m = new Method(md);
	// if (!m.isAnonymous())
	// System.out.println(m);
	// }
	// }

	// for (Feature f : methoddecl_map.keySet()) {
	// System.out.println("Feature " + f.getName()
	// + " provides following methods: ");
	// for (MethodDecl md : methoddecl_map.get(f)) {
	// System.out.print("\t" + md.hostType().name() + "@" + md.name()
	// + " ");
	// for (ParameterDeclaration pd : md.getParameters()) {
	// System.out.print(pd.getTypeAccess().typeName() + " ");
	// }
	// System.out.println();
	// // System.out.println(md.getTypeAccess());
	// }
	// }

    }

    class Method {
	String host_type;
	String type;
	String name;
	List<String> parameters = new ArrayList<String>();

	public Method(MethodDecl md) {
	    host_type = md.hostType().name();
	    if (md.type() instanceof UnknownType) {
		type = md.getTypeAccess().typeName();
	    } else {
		type = md.type().name();
	    }
	    name = md.name();
	    for (ParameterDeclaration pd : md.getParameters()) {
		if (pd.type() instanceof UnknownType) {
		    parameters.add(pd.getTypeAccess().typeName());
		} else {
		    parameters.add(pd.type().name());
		}
	    }
	}

	public Method(MethodAccess ma) {
	    host_type = ma.hostType().name();
	    type = ma.typeName();
	    name = ma.name();
	    for (Expr e : ma.getArgs()) {
		if (e.type() instanceof UnknownType) {
		    if (e instanceof VarAccess) {
			ASTNode p = ma.getParent();
			while(!(p instanceof CompilationUnit))
			    p = p.getParent();
			
			System.out.println(((CompilationUnit) p).pathName());
			System.out.println(((VarAccess) e).name() + " @ " + e.lineNumber());
		    }
		} else {
		    // System.out.println(e.type().name());
		}
	    }
	}

	public boolean isAnonymous() {
	    if (host_type.contains("Anonymous")) {
		return true;
	    } else {
		return false;
	    }
	}

	public String toString() {
	    StringBuilder builder = new StringBuilder();
	    builder.append(type).append(" ").append(host_type).append(".")
		    .append(name).append("(");
	    for (int i = 0; i < parameters.size(); i++) {
		builder.append(parameters.get(i));
		if (i < parameters.size() - 1) {
		    builder.append(", ");
		}
	    }
	    builder.append(")");
	    return builder.toString();
	}
    }
}
