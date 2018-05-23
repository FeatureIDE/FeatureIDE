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
import AST.TypeDecl;
import AST.UnknownType;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author Soenke Holthusen
 * @deprecated {@link TypeReferenceCheck} finds all missing superclass errors
 */

public class SuperClassCheck extends AbstractTypeCheckPlugin {
    private Map<Feature, List<ReferenceType>> intros;

    public SuperClassCheck() {
	plugin_name = "SuperClassCheck";
	registerNodeType(ClassDecl.class);
	registerNodeType(CompilationUnit.class);
    }

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
     * @see de.ovgu.featureide.core.typecheck.checks.ICheckPlugin#invokeCheck()
     */
    @Override
    public void invokeCheck(FeatureModel fm) {
	Map<Feature, List<ClassDecl>> map = getNodesByType(ClassDecl.class);

	for (Feature f : map.keySet()) {
	    for (ClassDecl cd : map.get(f)) {
		if (cd.hasSuperClassAccess()
			&& cd.getSuperClassAccess().type() instanceof UnknownType) {
		    Set<Feature> providing_features = providesType(
			    cd.getSuperClassAccess().typeName()).keySet();
		    if (checkFeatureImplication(fm, f, providing_features)) {
		    } else {
			newProblem(new CheckProblem(f, cd, cd.compilationUnit()
				.pathName(), cd.getSuperClassAccess()
				.lineNumber(), "Missing superclass "
				+ cd.getSuperClassAccess().typeName(), providing_features));
		    }
		}
	    }
	}
    }

    private Map<Feature, ReferenceType> providesType(String type) {
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

    /* (non-Javadoc)
     * @see de.ovgu.featureide.core.typecheck.check.ICheckPlugin#determineAction(de.ovgu.featureide.core.typecheck.check.CheckProblem)
     */
    @Override
    public List<Action> determineActions(CheckProblem problem) {
	// TODO Auto-generated method stub
	return null;
    }
}
