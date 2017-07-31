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

import AST.CompilationUnit;
import AST.FieldDeclaration;
import AST.TypeDecl;
import AST.VarAccess;
import AST.VariableDeclaration;
import de.ovgu.featureide.core.typecheck.correction.Action;
import de.ovgu.featureide.core.typecheck.helper.FujiWrapper;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author soenke
 */
public class FieldCheck extends AbstractTypeCheckPlugin {

    Map<Feature, Map<TypeDecl, List<FieldDeclaration>>> field_intros;

    /**
     * 
     */
    public FieldCheck() {
	plugin_name = "FieldCheck";
	registerNodeType(FieldDeclaration.class);
	registerNodeType(VarAccess.class);
    }

    /*
     * (non-Javadoc)
     * 
     * @see de.ovgu.featureide.core.typecheck.check.ICheckPlugin#init()
     */
    @Override
    public void init() {
	field_intros = new HashMap<Feature, Map<TypeDecl, List<FieldDeclaration>>>();

	Map<Feature, List<FieldDeclaration>> fields = getNodesByType(FieldDeclaration.class);

	for (Feature f : fields.keySet()) {
	    if (!field_intros.containsKey(f)) {
		field_intros.put(f,
			new HashMap<TypeDecl, List<FieldDeclaration>>());
	    }
	    Map<TypeDecl, List<FieldDeclaration>> fmap = field_intros.get(f);
	    for (FieldDeclaration fd : fields.get(f)) {
		if (!fmap.containsKey(fd.hostType())) {
		    fmap.put(fd.hostType(), new ArrayList<FieldDeclaration>());
		}

		fmap.get(fd.hostType()).add(fd);
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
	Map<Feature, List<VarAccess>> vars = getNodesByType(VarAccess.class);

	for (Feature f : vars.keySet()) {
	    for (VarAccess va : vars.get(f)) {
		if (va.isFieldAccess()) {
		    // checks if the host type is external
		    if (!FujiWrapper.getParentByType(va.decl().hostType(),
			    CompilationUnit.class).fromSource()) {
			continue;
		    }

		    // System.out.println("Looking for "
		    // + va.decl().hostType().name() + "." + va.name());

		    Map<Feature, FieldDeclaration> providing_features = providesField(va);

		    if (providing_features.isEmpty()) {
			System.out
				.println("Couldn't find a fielddeclaration for "
					+ va);
		    } else {
			// System.out.println("Found " +
			// providing_features.size()
			// + " providing features");
		    }

		    if (!checkFeatureImplication(fm, f,
			    providing_features.keySet())) {
			System.out.println("Missing Feature dependency!!11");
		    }
		} else if (va.decl() instanceof VariableDeclaration) {
		    VariableDeclaration vd = (VariableDeclaration) va.decl();
		    System.out.println(vd.getTypeAccess().typeName());
		}
	    }
	}

    }

    public Map<Feature, FieldDeclaration> providesField(VarAccess va) {
	Map<Feature, FieldDeclaration> providing_features = new HashMap<Feature, FieldDeclaration>();

	for (Feature f : field_intros.keySet()) {
	    for (TypeDecl td : field_intros.get(f).keySet()) {
		// if (va.decl().hostType().equals(td)) {
		if (va.decl().hostType().name().equals(td.name())) {
		    for (FieldDeclaration fd : field_intros.get(f).get(td)) {
			// if(va.decl().equals(fd)){
			if (va.name().equals(fd.name())) {
			    providing_features.put(f, fd);
			}
		    }
		}
	    }
	}

	return providing_features;
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
	// TODO Auto-generated method stub
	return null;
    }

}
