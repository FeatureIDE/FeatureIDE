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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ImportDecl;
import AST.InterfaceDecl;
import AST.TypeAccess;
import AST.TypeDecl;
import AST.UnknownType;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class TypeCheck extends AbstractCheckPlugin {

    private Map<String, List<Map<Feature, TypeDecl>>> classtable;

    public TypeCheck() {
	plugin_name = "Type Check Plugin";
	registerNodeType(TypeAccess.class);
	registerNodeType(ClassDecl.class);
	registerNodeType(InterfaceDecl.class);
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#invokeCheck(de.ovgu
     * .featureide.core.IFeatureProject,
     * de.ovgu.featureide.core.typecheck.parser.ClassTable)
     */
    @Override
    public void invokeCheck(IFeatureProject project, ClassTable class_table) {
	Map<Feature, List<TypeAccess>> map = getNodesByType(TypeAccess.class);

	for (Feature f : map.keySet()) {
	    System.out.println("Checking Feature " + f.getName());
	    for (TypeAccess ta : map.get(f)) {
		if (ta.type() instanceof UnknownType) {

		    TypeDecl td = ta.type().lookupType(ta.packageName(),
			    ta.name());
		    if (td == null) {
			System.out
				.println("Lookup for "
					+ ta.typeName()
					+ " was not successful, but following features may provide it:");
			for (Map<Feature, TypeDecl> m : getProvidingFeatures(ta
				.name())) {
			    if (m != null) {
				for (Feature pf : m.keySet()) {
				    System.out.println("\t" + pf.getName());
				}
			    }
			}
		    } else {
			System.out.println(td.fullName());
		    }

		    // ASTNode parent = ta.getParent();
		    // while (!(parent instanceof CompilationUnit)) {
		    // parent = parent.getParent();
		    // }
		    //
		    // isImported((CompilationUnit) parent, ta);
		    //
		    // if (getProvidingFeatures(ta.name()).size() == 0) {
		    // System.out.println("no feature provides "
		    // + ta.packageName() + ta.typeName());
		    // }

		    // System.out.println(ta.typeName()
		    // + " is unknown to feature " + f.getName());
		    // for (Feature feature :
		    // getProvidingFeatures(ta.typeName())
		    // .keySet()) {
		    // System.out.println("\tFeature " + feature.getName()
		    // + " can provide type " + ta.typeName());
		    // }
		}
	    }
	}
    }

    private boolean isImported(CompilationUnit cu, TypeAccess ta) {
	System.out.println(cu.pathName());
	for (ImportDecl id : cu.getImportDeclList()) {
	    System.out.println(id.typeName());
	}
	return false;
    }

    // TODO: cache results
    private List<Map<Feature, TypeDecl>> getProvidingFeatures(String type) {

	if (classtable == null) {
	    initCT();
	}

	if(classtable.containsKey(type)){
	return classtable.get(type);
	} else {
	    return null;
	}

	// for (Feature f : getNodesByType(ClassDecl.class).keySet()) {
	// for (ClassDecl cd : getNodesByType(ClassDecl.class).get(f)) {
	// if (cd.name().equals(type)) {
	// map.put(f, cd);
	// }
	// }
	// }
	//
	// for (Feature f : getNodesByType(InterfaceDecl.class).keySet()) {
	// for (InterfaceDecl cd : getNodesByType(InterfaceDecl.class).get(f)) {
	// if (cd.name().equals(type)) {
	// map.put(f, cd);
	// }
	// }
	// }
	//
	// return map;
    }

    protected void initCT() {
	classtable = new HashMap<String, List<Map<Feature, TypeDecl>>>();

	Map<Feature, List<ClassDecl>> class_map = getNodesByType(ClassDecl.class);

	for (Feature f : class_map.keySet()) {
	    for (ClassDecl cd : class_map.get(f)) {
		if (!classtable.containsKey(cd.typeName())) {
		    classtable.put(cd.typeName(),
			    new ArrayList<Map<Feature, TypeDecl>>());
		}
		Map<Feature, TypeDecl> map2 = new HashMap<Feature, TypeDecl>();
		map2.put(f, cd);
		classtable.get(cd.typeName()).add(map2);
	    }
	}

	Map<Feature, List<InterfaceDecl>> import_map = getNodesByType(InterfaceDecl.class);

	for (Feature f : import_map.keySet()) {
	    for (InterfaceDecl cd : import_map.get(f)) {
		if (!classtable.containsKey(cd.typeName())) {
		    classtable.put(cd.typeName(),
			    new ArrayList<Map<Feature, TypeDecl>>());
		}
		Map<Feature, TypeDecl> map2 = new HashMap<Feature, TypeDecl>();
		map2.put(f, cd);
		classtable.get(cd.typeName()).add(map2);
	    }
	}
    }

    protected String printCT() {
	StringBuilder builder = new StringBuilder();

	for (String type : classtable.keySet()) {
	    builder.append(type + " is defined in features\n");
	    for (Map<Feature, TypeDecl> map : classtable.get(type)) {
		for (Feature f : map.keySet()) {
		    builder.append("\t" + f.getName() + "\n");
		}
	    }
	}

	return builder.toString();
    }
}
