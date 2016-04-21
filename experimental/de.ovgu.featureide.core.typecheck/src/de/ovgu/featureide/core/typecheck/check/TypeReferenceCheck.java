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
import java.util.Set;

import AST.ClassDecl;
import AST.CompilationUnit;
import AST.ReferenceType;
import AST.TypeAccess;
import AST.TypeDecl;
import AST.UnknownType;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.core.typecheck.helper.FujiWrapper;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * Checks if every accessed type in a feature is reachable
 * 
 * @author Soenke Holthusen
 */
public class TypeReferenceCheck extends AbstractTypeCheckPlugin {
    private Map<Feature, List<ReferenceType>> intros;

    public TypeReferenceCheck() {
	plugin_name = "Type Check Plugin";
	registerNodeType(ClassDecl.class);
	registerNodeType(CompilationUnit.class);
	registerNodeType(TypeAccess.class);
    }

    /**
     * creates an introduction table which feature introduces which type?
     */
    public void init() {
	Map<Feature, List<CompilationUnit>> cumap = getNodesByType(CompilationUnit.class);

	intros = new HashMap<Feature, List<ReferenceType>>();
	for (Feature f : cumap.keySet()) {
	    if (!intros.containsKey(f)) {
		intros.put(f, new ArrayList<ReferenceType>());
	    }
	    for (CompilationUnit cu : cumap.get(f)) {
		for (TypeDecl td : cu.getTypeDecls()) {
		    if (td instanceof ReferenceType) {
			ReferenceType rt = (ReferenceType) td;
			if (!(rt.isAnonymous() || rt.isLocalClass() || rt
				.isArrayDecl())) {
			    intros.get(f).add(rt);
			}
		    }
		}
	    }
	}
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
    public void invokeCheck(FeatureModel fm) {
	// doesn't work with annotations and stuff
	// Map<Feature, List<ClassDecl>> cdmap =
	// getNodesByType(ClassDecl.class);
	Map<Feature, List<CompilationUnit>> cdmap = getNodesByType(CompilationUnit.class);
	int count = 0;

	for (Feature f : cdmap.keySet()) {
	    for (CompilationUnit cd : cdmap.get(f)) {
		// for every type access inside a class declaration
		for (TypeAccess ta : FujiWrapper.getChildNodesByType(cd,
			TypeAccess.class)) {
		    // for(TypeAccess ta : tamap.get(f)){
		    // utilise the type resolution of fuji and handle only
		    // unknown types
		    count++;
		    if (ta.type() instanceof UnknownType) {
			// which feature can provide the unknown type?
			Set<Feature> providing_features = providesType(
				ta.name()).keySet();

			if (providing_features.isEmpty()) {
			    CheckProblem problem = new CheckProblem(
				    f,
				    ta.hostType(),
				    cd.pathName(),
				    ta.lineNumber(),
				    "Class "
					    + ta.name()
					    + " can not be accessed in Feature "
					    + f.getName(), null);
			    problem.setSeverity(CheckProblem.SEVERITY_ERROR);

			    newProblem(problem);
			} else if (!checkFeatureImplication(fm, f,
				providing_features)) {
			    // it is not, create a new problem
			    CheckProblem problem = new CheckProblem(
				    f,
				    ta.hostType(),
				    cd.pathName(),
				    ta.lineNumber(),
				    "Class "
					    + ta.name()
					    + " can not be accessed in Feature "
					    + f.getName(), providing_features);
			    problem.setSeverity(CheckProblem.SEVERITY_WARNING);
			    newProblem(problem);
			}
		    }
		}
	    }
	}
	System.out.println(count + " typeaccesses");
    }

    protected Map<Feature, ReferenceType> providesType(String type) {
	Map<Feature, ReferenceType> providing_features = new HashMap<Feature, ReferenceType>();

	for (Feature f : intros.keySet()) {
	    for (ReferenceType rt : intros.get(f)) {
		if (rt.name().equals(type)) {
		    providing_features.put(f, rt);
		}
	    }
	}

	return providing_features;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#determineAction(
     * de.ovgu.featureide.core.typecheck.check.CheckProblem)
     */
    @Override
    public List<Action> determineActions(CheckProblem problem) {
	List<Action> actions = new ArrayList<Action>();
	actions.add(new Action());
	return actions;
    }
}
