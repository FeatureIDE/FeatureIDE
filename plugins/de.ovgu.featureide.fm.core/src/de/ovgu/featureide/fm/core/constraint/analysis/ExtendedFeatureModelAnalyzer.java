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
package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.List;

import org.sat4j.specs.TimeoutException;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class ExtendedFeatureModelAnalyzer extends FeatureModelAnalyzer  {

	private ExtendedFeatureModel efm;
	private BiMap<String, Integer> map;
	private List<DeRestriction> deFm;
	
	private UniqueId idGen;
	private RestrictionFactory<DeRestriction> deFactory;

	public ExtendedFeatureModelAnalyzer(FeatureModel fm) {
		super(fm);

		this.efm = (ExtendedFeatureModel) fm;
		this.idGen = new UniqueId();
		this.map = Translator.buildFeatureNameMap(efm, idGen);
		this.deFactory = new DeRestrictionFactory();
	}

	
	@Override
	public boolean isValid() throws TimeoutException {		
		if (deFm == null)
			setUpDeRestrictions();
		
		PBSolver solver = new SAT4JPBSolver();
		solver.addRestrictions(deFm);
		
		return solver.isSatisfiable();
	}

	
	private void setUpDeRestrictions() {
		this.deFm = Translator.translateFmTree(map, efm, deFactory);
		this.deFm.addAll(Translator.translateFmConstraints(map, efm, deFactory));
		this.deFm.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), deFactory));
	}

	
	/**
	 * @param atomicSets
	 * @param feature
	 * @category atomic set helper
	 */
	private static void newTreeAtomicSet(AtomicSets atomicSets, Feature feature) {
		int newId = atomicSets.newSet(feature);
		if (feature.hasChildren())
			processAtomicSetsOfChildren(atomicSets, newId, feature);
	}
	
	/**
	 * @param atomicSets
	 * @param newId
	 * @param feature
	 * @category atomic set helper
	 */
	private static void useTreeAtomicSet(AtomicSets atomicSets, int newId,
			Feature feature) {

		if (feature.isMandatory()) {
			atomicSets.add(newId, feature);
			if (feature.hasChildren())
				processAtomicSetsOfChildren(atomicSets, newId, feature);
		} else {
			newTreeAtomicSet(atomicSets, feature);
		}
	}
	

	/**
	 * @param atomicSets
	 * @param newId
	 * @param feature
	 * @category atomic set helper
	 */
	private static void processAtomicSetsOfChildren(AtomicSets atomicSets, 
			int newId, Feature feature) {

		if (feature.isAnd()) {
			for (Feature childFeature : feature.getChildren()) {
				useTreeAtomicSet(atomicSets, newId, childFeature);
			}
		} else {
			for (Feature childFeature : feature.getChildren()) {
				newTreeAtomicSet(atomicSets, childFeature);
			}
		}
	}

}
