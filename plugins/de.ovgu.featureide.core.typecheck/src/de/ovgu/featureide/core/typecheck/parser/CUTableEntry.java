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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;

import AST.Access;
import AST.ClassDecl;
import AST.ClassInstanceExpr;
import AST.CompilationUnit;
import AST.IntrosRefsUtil;
import AST.MethodDecl;
import AST.Opt;
import AST.ReferenceType;
import AST.TypeDecl;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author soenke
 */
public class CUTableEntry {
	private CompilationUnit cu;
	//private Feature feature;
	private String feature_path;

	private List<ReferenceType> introduced_types;
	private List<MethodDecl> introduced_methods;
	
	private HashMap<String, List<String>> methods_by_type = new HashMap<String, List<String>>();

	private List<Access> referenced_subtyping_types;

	/**
	 * 
	 * @param cu
	 * @param feature_path
	 * @param feature
	 */
	public CUTableEntry(CompilationUnit cu, String feature_path, Feature feature) {
		this.cu = cu;
		//this.feature = feature;
		this.feature_path = feature_path;
	}

	protected void parse(){
		List<MethodDecl> methods = FujiWrapper.getMethodDecls(cu);
		for(MethodDecl method : methods){
			List<String> list = this.methods_by_type.get(method.hostType().name());
			if(list == null){
				list = new ArrayList<String>();
				this.methods_by_type.put(method.hostType().name(), list);
			}
			
			list.add(method.signature());
		}
	}
	
	public boolean providesType(String type) {
		for (ReferenceType ref : getIntroducedTypes()) {
			// TODO: check what format .name() has
			if (ref.name().equals(type)) {
				System.out.println(ref.name() + " matches " + type);
				return true;
			}
		}
		return false;
	}

	/**
	 * @param signature
	 * @return
	 */
	public boolean providesMethod(String type, String signature) {
		if (providesType(type)) {
			for (MethodDecl method : getIntroducedMethods()) {
				if (IntrosRefsUtil.signature(method).equals(signature)) {
					System.out.println(IntrosRefsUtil.signature(method)
							+ " matches " + signature);
					return true;
				}
			}
		}
		return false;
	}

	public String printIntroducedTypes() {
		StringBuilder builder = new StringBuilder();

		List<String> path = new LinkedList<String>();
		path.add(feature_path);

		for (ReferenceType rt : getIntroducedTypes()) {
			builder.append(IntrosRefsUtil.introPrefix(rt, path));
			builder.append(IntrosRefsUtil.typeDeclQName(rt)).append("\n");
		}

		return builder.toString();
	}

	public List<ReferenceType> getIntroducedTypes() {
		if (introduced_types == null) {
			introduced_types = new ArrayList<ReferenceType>();

			List<String> path = new LinkedList<String>();
			path.add(feature_path);
			java.util.Collection<ReferenceType> refiningTypes = cu
					.getRefiningTypes();

			if (refiningTypes != null) {
				for (ReferenceType rt : refiningTypes) {
					if (!(rt.isAnonymous() || rt.isLocalClass() || rt
							.isArrayDecl())) {
						introduced_types.add(rt);
					}
				}
			}
		}
		return introduced_types;
	}

	public String printIntroducedMethods() {
		List<String> path = new LinkedList<String>();
		path.add(feature_path);
		StringBuilder intro = new StringBuilder();
		for (MethodDecl method : getIntroducedMethods()) {
			TypeDecl host = IntrosRefsUtil.visibleHostType(method);

			intro.append(IntrosRefsUtil.introPrefix(method, path))
					.append(IntrosRefsUtil.typeDeclQName(host))
					.append(IntrosRefsUtil.DELIM_METHOD
							+ IntrosRefsUtil.signature(method))
					.append(IntrosRefsUtil.DELIM_TYPE)
					.append(method.type().typeName()).append("\n");
		}
		return intro.toString();
	}

	public List<MethodDecl> getIntroducedMethods() {
		if (introduced_methods == null) {
			introduced_methods = FujiWrapper.getMethodDecls(cu);
		}

		return introduced_methods;
	}

	public List<Access> getReferencedSubtypingTypes() {
		if (referenced_subtyping_types == null) {
			referenced_subtyping_types = new ArrayList<Access>();

			for (TypeDecl type : cu.getTypeDeclList()) {
				if (type instanceof ClassDecl) {
					ClassDecl clas = (ClassDecl) type;
					if (clas.hasSuperClassAccess()) {
						Opt<Access> ext = clas.getSuperClassAccessOpt();
						for (int i = 0; i < ext.getNumChild(); ++i) {
							Access ac = ext.getChild(i);
							referenced_subtyping_types.add(ac);
						}
					}
					// TODO: get access for preservedSuperClassAccesses
					// for (Access ac : clas.preservedSuperClassAccesses) {
					// referenced_subtyping_types.add(ac);
					// }
					if (clas.getImplementsList().getNumChild() != 0) {
						AST.List<Access> imp = clas.getImplementsList();
						for (int i = 0; i < imp.getNumChild(); ++i) {
							Access ac = imp.getChild(i);
							referenced_subtyping_types.add(ac);
						}
					}
				}
			}
		}

		return referenced_subtyping_types;
	}

    public List<ClassInstanceExpr> getClassInstance() {
	return null;
    }
}
