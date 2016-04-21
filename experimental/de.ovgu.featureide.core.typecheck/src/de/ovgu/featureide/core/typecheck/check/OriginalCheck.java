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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import AST.CompilationUnit;
import AST.MethodAccess;
import AST.MethodDecl;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.core.typecheck.helper.FujiWrapper;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 */
public class OriginalCheck extends AbstractTypeCheckPlugin {
    private Map<Feature, List<MethodDecl>> method_intros;

    public OriginalCheck() {
	plugin_name = "original() Check";
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
	method_intros = new HashMap<Feature, List<MethodDecl>>();

	Map<Feature, List<MethodDecl>> method_map = getNodesByType(MethodDecl.class);

	for (Feature f : method_map.keySet()) {
	    if (!method_intros.containsKey(f)) {
		method_intros.put(f, new ArrayList<MethodDecl>());
	    }

	    for (MethodDecl md : method_map.get(f)) {
		method_intros.get(f).add(md);
	    }
	}
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#invokeCheck(de.ovgu
     * .featureide.fm.core.FeatureModel)
     */
    @Override
    public void invokeCheck(FeatureModel fm) {
	Map<Feature, List<MethodAccess>> method_accesses = getNodesByType(MethodAccess.class);

	for (Feature f : method_accesses.keySet()) {
	    for (MethodAccess ma : method_accesses.get(f)) {
		if (ma.name().equals("original")) {
		    MethodDecl md = FujiWrapper.getParentByType(ma,
			    MethodDecl.class);

		    Map<Feature, MethodDecl> providing_features = new HashMap<Feature, MethodDecl>();
		    if (fm.getFeatureOrderList().isEmpty()) {
			List<Feature> feature_list = getFeatureList(fm
				.getRoot());
			providing_features = providesOriginal(
				getPredecessorFeatures(feature_list, f), md);
		    } else {
			providing_features = providesOriginal(
				getPredecessorFeatures(fm, f), md);
		    }

		    if (providing_features.isEmpty()) {
			CheckProblem problem = new CheckProblem(f,
				md.hostType(), FujiWrapper.getParentByType(md,
					CompilationUnit.class)
				// .compilationUnit()
					.pathName(), ma.lineNumber(),
				"original() method not found: "
					+ md.signature(), null);
			problem.setSeverity(CheckProblem.SEVERITY_ERROR);
			newProblem(problem);
		    } else {
			if (!checkFeatureImplication(fm, f,
				providing_features.keySet())) {
			    CheckProblem problem = new CheckProblem(f,
				    md.hostType(), FujiWrapper.getParentByType(
					    md, CompilationUnit.class)
					    .pathName(), ma.lineNumber(),
				    // "Missing dependency to original() method: "
				    "Method " + md.hostType().name() + "."
					    + md.signature()
					    + " can not be accessed in Feature"
					    + f.getName() + ".",
				    providing_features.keySet());
			    problem.setSeverity(CheckProblem.SEVERITY_WARNING);
			    newProblem(problem);
			}
		    }
		}
	    }
	}
    }

    private Map<Feature, MethodDecl> providesOriginal(
	    List<Feature> predecessors, MethodDecl original) {
	Map<Feature, MethodDecl> providing_features = new HashMap<Feature, MethodDecl>();
	for (Feature f : predecessors) {
	    if (method_intros.containsKey(f)) {
		for (MethodDecl md : method_intros.get(f)) {
		    if (md.hostType().name().equals(original.hostType().name())) {
			if (md.name().equals(original.name())
				&& md.getNumParameter() == original
					.getNumParameter()) {
			    providing_features.put(f, md);
			}
		    }
		}
	    }
	}
	return providing_features;
    }

    private List<Feature> getPredecessorFeatures(FeatureModel fm, Feature f) {
	List<Feature> predecessors = new LinkedList<Feature>();
	for (String feature : fm.getFeatureOrderList()) {
	    if (feature.equals(f.getName())) {
		break;
	    }
	    predecessors.add(fm.getFeature(feature));
	}
	// TODO: figure out, why f is added to the list and has to be removed
	// manually
	predecessors.remove(f);
	return predecessors;
    }

    private List<Feature> getPredecessorFeatures(List<Feature> features,
	    Feature f) {
	List<Feature> predecessors = new LinkedList<Feature>();
	for (Feature feature : features) {
	    if (feature.equals(f)) {
		break;
	    }
	    predecessors.add(feature);

	}
	// TODO: figure out, why f is added to the list and has to be removed
	// manually
	predecessors.remove(f);
	return predecessors;
    }

    private List<Feature> getFeatureList(Feature root) {
	List<Feature> features = new ArrayList<Feature>();
	if (!root.isAbstract()) {
	    features.add(root);
	}
	for (Feature c : root.getChildren()) {
	    features.addAll(getFeatureList(c));
	}
	return features;
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.ovgu.featureide.core.typecheck.check.ICheckPlugin#determineActions
     * (de.ovgu.featureide.core.typecheck.check.CheckProblem)
     */
    @Override
    public List<Action> determineActions(CheckProblem problem) {
	List<Action> actions = new ArrayList<Action>();
	actions.add(new Action());
	return actions;
    }

}
