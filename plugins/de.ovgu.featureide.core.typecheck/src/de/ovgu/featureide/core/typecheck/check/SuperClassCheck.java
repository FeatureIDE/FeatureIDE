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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import AST.ClassDecl;
import AST.TypeAccess;
import AST.UnknownType;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.typecheck.parser.ClassTable;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

/**
 * TODO description
 * 
 * @author S�nke Holthusen
 */

public class SuperClassCheck extends AbstractCheckPlugin {
	public SuperClassCheck() {
		plugin_name = "SuperClassCheck";
		registerNodeType(ClassDecl.class);
		registerNodeType(TypeAccess.class);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.ovgu.featureide.core.typecheck.checks.ICheckPlugin#invokeCheck()
	 */
	@Override
	public void invokeCheck(FeatureModel fm) {
		Map<Feature, List<ClassDecl>> map = getNodesByType(ClassDecl.class);
		for (Feature key : map.keySet()) {
			for (ClassDecl cd : map.get(key)) {
				if(cd.hasSuperClassAccess() && cd.getSuperClassAccess().type() instanceof UnknownType){
					System.out.println("Unknown Type: " + cd.getSuperClassAccess().typeName() + " in Feature " + key.getName());
					System.out.println("\t can be provided by");
					Set<Feature> providing_features = providesType(map, cd.getSuperClassAccess().typeName()).keySet();
					for(Feature f : providing_features){
						System.out.println("\t\t" + f.getName());
					}
					if(checkFeatureImplication(fm, key, providing_features)){
						System.out.print("\t\t\t" + key.getName() + " -> ");
						for(Feature f : providing_features){
							System.out.print(f.getName() + " ");
						}
						System.out.println(" holds!");
					}
					else {
						System.out.println("Missing dependency!!!");
					}
				}
			}
		}
	}

	private Map<Feature, ClassDecl> providesType(
			Map<Feature, List<ClassDecl>> map, String type) {
		Map<Feature, ClassDecl> providing_features = new HashMap<Feature, ClassDecl>();

		for (Feature f : map.keySet()) {
			for (ClassDecl cd : map.get(f)) {
				if (cd.name().equals(type)) {
					providing_features.put(f, cd);
				}
			}
		}

		return providing_features;
	}
}
