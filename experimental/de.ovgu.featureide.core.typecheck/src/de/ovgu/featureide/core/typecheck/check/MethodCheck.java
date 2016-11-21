/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
 *
 * This file is part of FeatureIDE.
 * 
 * FeatureIDE is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * FeatureIDE is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with FeatureIDE.  If not, see <http://www.gnu.org/licenses/>.
 *
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package de.ovgu.featureide.core.typecheck.check;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import AST.ClassDecl;
import AST.CompilationUnit;
import AST.Expr;
import AST.MethodAccess;
import AST.MethodDecl;
import AST.ParameterDeclaration;
import AST.UnknownType;
import AST.VarAccess;
import AST.Variable;
import AST.VariableDeclaration;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.core.typecheck.helper.FujiWrapper;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * NYI
 * 
 * @author Soenke Holthusen
 */
public class MethodCheck extends AbstractTypeCheckPlugin {

    private Map<Feature, Map<String, List<MethodDecl>>> method_intros;

    public MethodCheck() {
	plugin_name = "MethodAccess Check";
	registerNodeType(MethodAccess.class);
	registerNodeType(MethodDecl.class);
    }

    @Override
    public void init() {
	method_intros = new HashMap<Feature, Map<String, List<MethodDecl>>>();

	Map<Feature, List<MethodDecl>> method_map = getNodesByType(MethodDecl.class);

	for (Feature f : method_map.keySet()) {
	    if (!method_intros.containsKey(f)) {
		method_intros.put(f, new HashMap<String, List<MethodDecl>>());
	    }

	    Map<String, List<MethodDecl>> map = method_intros.get(f);
	    for (MethodDecl md : method_map.get(f)) {
		if (!map.containsKey(md.hostType().name())) {
		    map.put(md.hostType().name(), new ArrayList<MethodDecl>());
		}
		map.get(md.hostType().name()).add(md);
	    }
	}

	// for (Feature f : method_map.keySet()) {
	// method_intros.put(f, new HashMap<TypeDecl, List<Method>>());
	// Map<TypeDecl, List<Method>> methods = method_intros.get(f);
	// for (MethodDecl md : method_map.get(f)) {
	// if (!(methods.containsKey(md.hostType().name()))) {
	// methods.put(md.hostType(),
	// new ArrayList<MethodCheck.Method>());
	// }
	//
	// methods.get(md.hostType().name()).add(new Method(md));
	// }
	// }
	//
	// for (Feature f : method_intros.keySet()) {
	// for (TypeDecl s : method_intros.get(f).keySet()) {
	// for (Method m : method_intros.get(f).get(s)) {
	// System.out.println(f + ":" + m);
	// }
	// }
	// }
    }

    @Override
    public void invokeCheck(FeatureModel fm) {
	// Map<Feature, List<MethodDecl>> methoddecl_map =
	// getNodesByType(MethodDecl.class);
	Map<Feature, List<MethodAccess>> methodaccess_map = getNodesByType(MethodAccess.class);
	//
	for (Feature f : methodaccess_map.keySet()) {
	    for (MethodAccess ma : methodaccess_map.get(f)) {
//		System.out.println(ma.name());
//		if (!FujiWrapper.getParentByType(ma.decl().hostType(),
//			CompilationUnit.class).fromSource()) {
//		    continue;
//		}

		if (ma.decl().name().contains("Anonymous")) {
		    continue;
		}

		
		
		// System.out.println(ma.decl().hostType().name() + "."
		// + ma.name());

		List<String> args = argsToString(ma.getArgList());
		// for (String arg : args) {
		// System.out.println(arg);
		// }
		Map<Feature, List<MethodMatch>> providing_features = providesMethod(
			ma.decl().hostType().name(), ma.decl().name(), args);

		if (countMethodMatches(providing_features) == 0) {
		    if(ma.decl().hostType() instanceof UnknownType){
			System.out.println(ma.name());
			System.out.println(FujiWrapper.getParentByType(ma, CompilationUnit.class).pathName() + ":" + ma.lineNumber());
			System.out.println(FujiWrapper.getParentByType(ma, ClassDecl.class).name());
			System.out.println(ma.getParent());
		    }
//		    System.out.println("Not found: "
//			    + ma.decl().hostType().name() + "." + ma.name());
		}

		// TODO: distinguish between different matches
//		for (Feature pf : providing_features.keySet()) {
//		    for (MethodMatch mm : providing_features.get(pf)) {
//			if (mm.type == MethodMatch.MATCH) {
//			    System.out.println("Match: ");
//			    System.out.println(printMA(ma) + " vs "
//				    + printMD(mm.md));
//			}
//			if (mm.type == MethodMatch.PARAMETER_MATCH) {
//			    System.out.println("Parametertypes don't match: ");
//			    System.out.println(printMA(ma) + " vs "
//				    + printMD(mm.md));
//			}
//			if (mm.type == MethodMatch.NAME_MATCH) {
//			    System.out
//				    .println("Parametercount doesn't match: ");
//			    System.out.println(printMA(ma) + " vs "
//				    + printMD(mm.md));
//			}
//		    }
//		}

		// if (providing_features.size() == 0) {

		// } else {
		// System.out.println("Found: " + ma.decl().hostType().name()
		// + "." + ma.name());
		// }
		// if (ma.type() instanceof UnknownType) {
		// System.out.println("unknown!!!");
		// System.out.println(ma.name());
		// } else {
		// System.out.println("known!!!");
		// }
		// Method m = new Method(ma);
		// if (!m.isAnonymous()) {
		// Collection<Feature> providing_features = providesMethod(m)
		// .keySet();
		// if (providing_features.size() == 0) {
		// System.out.println(m);
		// } else {
		// //System.out.println("Found something for " + m);
		// }
		// }
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

    private List<String> argsToString(AST.List<Expr> args) {
	List<String> argss = new ArrayList<String>();
	for (Expr e : args) {
	    if (e.type() instanceof UnknownType) {
		if (e instanceof VarAccess) {
		    Variable var = ((VarAccess) e).varDecl();

		    if (var instanceof VariableDeclaration) {
			VariableDeclaration vd = (VariableDeclaration) var;
			argss.add(vd.getTypeAccess().typeName());
		    } else if (var instanceof ParameterDeclaration) {
			ParameterDeclaration pd = (ParameterDeclaration) var;
			argss.add(pd.getTypeAccess().typeName());
		    }
		}
	    } else {
		argss.add(e.type().name());
	    }
	}
	return argss;
    }

    private List<String> paramsToString(AST.List<ParameterDeclaration> params) {
	List<String> paramss = new ArrayList<String>();
	for (ParameterDeclaration pd : params) {
	    if (pd.type() instanceof UnknownType) {
		paramss.add(pd.getTypeAccess().typeName());
	    } else {
		paramss.add(pd.type().name());
	    }
	}
	return paramss;
    }

    private Map<Feature, List<MethodMatch>> providesMethod(String host_type,
	    String name, List<String> args) {
	Map<Feature, List<MethodMatch>> providing_features = new HashMap<Feature, List<MethodMatch>>();

	for (Feature f : method_intros.keySet()) {
	    if (method_intros.get(f).containsKey(host_type)) {
		for (MethodDecl md : method_intros.get(f).get(host_type)) {
		    if (md.name().equals(name)) {
			if (md.getNumParameter() == args.size()) {
			    if (compareMethodParameters(
				    paramsToString(md.getParameterList()), args)) {
				if (!providing_features.containsKey(f)) {
				    providing_features
					    .put(f,
						    new ArrayList<MethodCheck.MethodMatch>());
				}

				providing_features.get(f).add(
					new MethodMatch(MethodMatch.MATCH, md));
			    } else {
				if (!providing_features.containsKey(f)) {
				    providing_features
					    .put(f,
						    new ArrayList<MethodCheck.MethodMatch>());
				}
				providing_features
					.get(f)
					.add(new MethodMatch(
						MethodMatch.PARAMETER_MATCH, md));
			    }
			} else {
			    if (!providing_features.containsKey(f)) {
				providing_features
					.put(f,
						new ArrayList<MethodCheck.MethodMatch>());
			    }
			    providing_features.get(f)
				    .add(new MethodMatch(
					    MethodMatch.NAME_MATCH, md));
			}
		    }
		}
	    }
	}

	// for (Feature f : method_intros.keySet()) {
	// if (method_intros.get(f).containsKey(m.host_type)) {
	// for (Method method : method_intros.get(f).get(m.host_type)) {
	// MethodMatch mm = new MethodMatch();
	// if (method.name.equals(m.name)) {
	// mm.type = MethodMatch.NAME_MATCH;
	// if (method.parameters.size() == m.parameters.size()) {
	// mm.type = MethodMatch.PARAMETER_MATCH;
	// for (int i = 0; i < method.parameters.size(); i++) {
	// if (!method.parameters.get(i).equals(
	// m.parameters.get(i))) {
	// break;
	// }
	// if (i + 1 == method.parameters.size()) {
	// mm.type = MethodMatch.MATCH;
	// }
	// }
	// }
	// }
	// if (mm.type != MethodMatch.UNDEFINED) {
	// if (!providing_features.containsKey(f)) {
	// providing_features.put(f,
	// new ArrayList<MethodCheck.MethodMatch>());
	// providing_features.get(f).add(mm);
	// }
	// }
	// }
	// }
	// }
	return providing_features;
    }

    public boolean compareMethodParameters(List<String> parameters,
	    List<String> args) {

	for (int i = 0; i < parameters.size(); i++) {
	    if (!args.get(i).equals(parameters.get(i))) {
		return false;
	    }
	}

	return true;
    }

    public String printMA(MethodAccess ma) {
	StringBuilder builder = new StringBuilder();

	builder.append(ma.decl().hostType().name()).append(".")
		.append(ma.name());
	builder.append("(");
	List<String> args = argsToString(ma.getArgList());

	for (int i = 0; i < args.size(); i++) {
	    builder.append(args.get(i));
	    if (i < args.size() - 1) {
		builder.append(", ");
	    }
	}

	builder.append(")");

	return builder.toString();
    }

    public String printMD(MethodDecl md) {
	StringBuilder builder = new StringBuilder();

	builder.append(md.hostType().name()).append(".").append(md.name());
	builder.append("(");
	List<String> args = paramsToString(md.getParameterList());

	for (int i = 0; i < args.size(); i++) {
	    builder.append(args.get(i));
	    if (i < args.size() - 1) {
		builder.append(", ");
	    }
	}

	builder.append(")");

	return builder.toString();
    }

    private int countMethodMatches(Map<Feature, List<MethodMatch>> map){
	int count = 0;
	for(Feature f : map.keySet()){
	    count+=map.get(f).size();
	}
	return count;
    }
    
    class Method implements Comparable<Method> {
	MethodDecl md;
	String host_type;
	String type;
	String name;
	List<String> parameters = new ArrayList<String>();

	public Method(MethodDecl md) {
	    this.md = md;
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
			Variable var = ((VarAccess) e).varDecl();

			if (var instanceof VariableDeclaration) {
			    VariableDeclaration vd = (VariableDeclaration) var;
			    parameters.add(vd.getTypeAccess().typeName());
			} else if (var instanceof ParameterDeclaration) {
			    ParameterDeclaration pd = (ParameterDeclaration) var;
			    parameters.add(pd.getTypeAccess().typeName());
			} else {
			    System.out.println("something different");
			}
		    }
		} else {
		    parameters.add(e.type().name());
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

	public String getHostType() {
	    return host_type;
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

	@Override
	public int compareTo(Method o) {
	    int ret = host_type.compareTo(o.host_type);
	    if (ret != 0) {
		return ret;
	    }
	    // System.out.println(host_type + "==" + o.host_type);

	    ret = name.compareTo(o.name);
	    if (ret != 0) {

		return ret;
	    }
	    // System.out.println(name + "==" + o.name);

	    ret = parameters.size() - o.parameters.size();
	    if (ret != 0) {
		// System.out.println(parameters.size() + "!=" +
		// o.parameters.size());
		return ret;
	    }

	    for (int i = 0; i < parameters.size(); i++) {
		ret = parameters.get(i).compareTo(o.parameters.get(i));
		if (ret != 0) {
		    // System.out.println( parameters.get(i) + "!=" + o.
		    // parameters.get(i));
		    return ret;
		}
	    }

	    return ret;
	}

	public boolean equals(Method o) {
	    return compareTo(o) == 0;
	}

    }

    class MethodMatch {
	public static final int UNDEFINED = 0;
	public static final int NAME_MATCH = 1;
	public static final int PARAMETER_MATCH = 2;
	public static final int MATCH = 3;

	public MethodDecl md;
	public int type = UNDEFINED;

	public MethodMatch(int type, MethodDecl md) {
	    this.type = type;
	    this.md = md;
	}
    }

    @Override
    public List<Action> determineActions(CheckProblem problem) {
	// TODO Auto-generated method stub
	return null;
    }
}
