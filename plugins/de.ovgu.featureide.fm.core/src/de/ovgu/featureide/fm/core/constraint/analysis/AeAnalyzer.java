/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.List;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 */
public class AeAnalyzer implements IAeAnalyzer {

	private ExtendedFeatureModel efm;
	private BiMap<String, Integer> map;
//	private List<AeRestriction> aeFm;
	
	private UniqueId idGen;
//	private RestrictionFactory<AeRestriction> aeFactory;
	
	public AeAnalyzer(ExtendedFeatureModel efm) {
		this.efm = efm;
		this.idGen = new UniqueId();
		this.map = Translator.buildFeatureNameMap(efm, idGen);
//		this.aeFactory = new AeRestrictionFactory();
	}
	
	private List<AeRestriction> setUpAeRestrictions(RestrictionFactory<AeRestriction> factory) {
		List<AeRestriction> rs = Translator.translateFmTree(map, efm, factory);
		rs.addAll(Translator.translateFmConstraints(map, efm, factory));
		rs.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), factory));
		return rs;
	}
	
	@Override
	public Assignments getOptimalProduct() {
		return null;
	}

	@Override
	public Assignments propagate(List<Feature> enabledFeatures, List<Feature> disabledFeatures) 
			throws ContradictionException {
		
		BooleanConstraintPropagator propagator = new BooleanConstraintPropagator();
		
		List<AeRestriction> rs = 
			setUpAeRestrictions(new BCPRestrictionFactory(propagator));
		
		propagator.setUp(rs, efm, map);
		
		Assignments assignments =
			propagator.startPropagation(enabledFeatures, disabledFeatures);
		
		return assignments;
	}

	
}
