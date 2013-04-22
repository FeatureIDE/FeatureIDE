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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.constraint.analysis.AtomicSetMerger.Result;
import de.ovgu.featureide.fm.core.editing.Comparison;

/**
 * TODO description
 */
public class DeAnalyzer implements IDeAnalyzer {

	private ExtendedFeatureModel efm;
	private BiMap<String, Integer> map;
	private List<DeRestriction> deFm;
	private List<AsRestriction> asFm;
	
	private UniqueId idGen;
	private RestrictionFactory<DeRestriction> deFactory;
	private RestrictionFactory<AsRestriction> asFactory;
	
	private Set<Feature> coreFeatures = null;
	private Set<Feature> falseOptionalFeatures = null;
	private Set<Feature> variantFeatures = null;
	private Set<Feature> deadFeatures = null;
	private AtomicSets atomicSets = null;
	
	
	public DeAnalyzer(ExtendedFeatureModel efm) {
		this.efm = efm;
		this.idGen = new UniqueId();
		this.map = Translator.buildFeatureNameMap(efm, idGen);
		this.deFactory = new DeRestrictionFactory();
		this.asFactory = new AsRestrictionFactory();
	}	
	
	@Override
	public boolean isValid() {
		if (deFm == null)
			setUpDeRestrictions();
		
		PBSolver solver = new SAT4JPBSolver();
		solver.addRestrictions(deFm);
		return solver.isSatisfiable();
	}
	
	
	@Override
	public Set<Feature> getCoreFeatures() {
		if (coreFeatures == null) {
			computeFeatureProperties();
		}
		return coreFeatures;
	}

	@Override
	public Set<Feature> getDeadFeatures() {
		if (deadFeatures == null) {
			computeFeatureProperties();
		}
		return deadFeatures;
	}
	
	@Override
	public Set<Feature> getVariantFeatures() {
		if (variantFeatures == null) {
			computeFeatureProperties();
		}
		return variantFeatures;
	}
	
	@Override
	public Set<Feature> getFalseOptionalFeatures() {
		if (falseOptionalFeatures == null) {
			computeFeatureProperties();
		}
		return falseOptionalFeatures;
	}
	
	
	@Override
	public AtomicSets getAtomicSets() {
		// use cached result if available
		if (atomicSets != null) {
			return atomicSets;
		}
		
		// set up the list of atomic set restrictions
		setUpAsRestrictions();
//		System.out.println("#features:     " + map.size());
//		System.out.println("#restrictions: " + asFm.size());
		
		System.out.println(map);
		
		// traverse the feature diagram, collect strongly connected components
		// and remove redundant restrictions
		atomicSets = new AtomicSets(map);
		newTreeAtomicSet(atomicSets, efm.getRoot());
		List<AsRestriction> toRemove = new ArrayList<AsRestriction>();
		for (AsRestriction r : asFm) {
			if (r.fid2asid(atomicSets))
				toRemove.add(r);
		}
		asFm.removeAll(toRemove);
		
//		System.out.println("#tree at. set: " + atomicSets.size());	
//		System.out.println("#restrictions: " + asFm.size());
		
		AtomicSetMerger merger = new AtomicSetMerger(atomicSets, asFm);
		mergeRecursive(merger, atomicSets.getAtomicSetIds());
		
//		System.out.println("#real at. set: " + atomicSets.size());
//		System.out.println("#restrictions: " + asFm.size());
		
		return atomicSets;
	}

	@Override
	public Comparison getEditType(ExtendedFeatureModel newEfm) {
		if (deFm == null)
			setUpDeRestrictions();
		
		Translator.extendFeatureNameMap(map, newEfm, idGen);
		
		List<DeRestriction> fSimple = new ArrayList<DeRestriction>(deFm);
		
		// restrictions describing the new feature model
		List<DeRestriction> g = Translator.translateFmTree(map, newEfm, deFactory);
		g.addAll(Translator.translateFmConstraints(map, newEfm, deFactory));
		g.addAll(Translator.translateEquations(map, newEfm, newEfm.getIntegerAttributes(), 
				newEfm.getAttributConstraints(), deFactory));
		
		List<DeRestriction> gSimple = new ArrayList<DeRestriction>(g);
		
		
		Set<String> addedFeatures   = getAddedFeatures(efm, newEfm);
		Set<String> removedFeatures = getAddedFeatures(newEfm, efm);
		
		//gSimple.removeAll(f); // called "p_g" in paper
		for (DeRestriction restr : deFm) {
			gSimple.remove(restr);
		}
		//fSimple.removeAll(g); // called "p_f" in paper
		for (DeRestriction restr : g) {
			fSimple.remove(restr);
		}
		
		boolean fImpliesG = implies(deFm, addedFeatures, newEfm, gSimple);
		boolean gImpliesF = implies(g, removedFeatures, efm, fSimple);
		
		Comparison result;
		
		if (fImpliesG) {
			if (gImpliesF) {
				result = Comparison.REFACTORING;
			} else {
				result = Comparison.GENERALIZATION;
			}
		} else {
			if (gImpliesF) {
				result = Comparison.SPECIALIZATION;
			} else {
				result = Comparison.ARBITRARY;
			}
		}
		
		return result;
	}
	
	private void setUpDeRestrictions() {
		this.deFm = Translator.translateFmTree(map, efm, deFactory);
		this.deFm.addAll(Translator.translateFmConstraints(map, efm, deFactory));
		this.deFm.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), deFactory));
	}
	
	private void setUpAsRestrictions() {
		this.asFm = Translator.translateFmTree(map, efm, asFactory);
		this.asFm.addAll(Translator.translateFmConstraints(map, efm, asFactory));
		this.asFm.addAll(Translator.translateEquations(map, efm, 
				efm.getIntegerAttributes(), efm.getAttributConstraints(), asFactory));
	}

	/**
	 * @category feature property helper
	 */
	private void computeFeatureProperties() {
		if (deFm == null)
			setUpDeRestrictions();
		
		coreFeatures = new HashSet<Feature>();
		falseOptionalFeatures = new HashSet<Feature>();
		deadFeatures = new HashSet<Feature>();
		variantFeatures = new HashSet<Feature>();
		
		PBSolver solver = new SAT4JPBSolver();
		solver.addRestrictions(deFm);
		Set<Integer> backbone = solver.backbone(map.inverse().keySet());
		
		for (Integer variable : backbone) {
			if (variable > 0) {
				Feature coreFeature = efm.getFeature(map.inverse().get(variable));
				coreFeatures.add(coreFeature);
				
				if (isFalseOptional(coreFeature)) {
					falseOptionalFeatures.add(coreFeature);
				}
			} else if (variable < 0) {
				Feature deadFeature = efm.getFeature(map.inverse().get(-variable));
				deadFeatures.add(deadFeature);
			}
		}
		for (Feature feature : efm.getFeatures()) {
			if (!coreFeatures.contains(feature) && !deadFeatures.contains(feature)) {
				variantFeatures.add(feature);
			}
		}
	}
	
	/**
	 * @param feature
	 * @return
	 * @category feature property helper
	 */
	private static boolean isFalseOptional(Feature feature) {
		Feature parent = feature.getParent();
		return !feature.isMandatory() && parent != null && parent.isAnd();
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
	
	/**
	 * @param merger
	 * @param vars
	 * @category atomic set helper
	 */
	private void mergeRecursive(AtomicSetMerger merger, Set<Integer> vars) {
		if (vars.contains(map.get("BerkeleyDB"))) {
			System.out.println(vars);
		}
		
		Result result = merger.tryMerge(new HashSet<Integer>(vars));
		if (!result.wasSuccessful()) {
			mergeRecursive(merger, result.getFirstPartition());
			mergeRecursive(merger, result.getSecondPartition());
		}
	}
	
	/**
	 * @param baseRestrictions
	 * @param virtualFeatures
	 * @param simplifiedRestrictions
	 * @return
	 * @category edit type helper
	 */
	private boolean implies(List<DeRestriction> baseRestrictions,
			Set<String> virtualFeatures, FeatureModel model,
			List<DeRestriction> simplifiedRestrictions) {
		// Extension for Adding and Removing Features
		for (String name : virtualFeatures) {
			if (model.getFeature(name).isAbstract()) {
				int toReplace = map.get(name);
				
				System.out.println("abstract:");
				System.out.println(toReplace);
				System.out.println(simplifiedRestrictions);
				
				
			} else {
				Translator.createAssumption(map.get(name), false, 
						baseRestrictions, deFactory);
			}
		}
		
		for (DeRestriction restr : simplifiedRestrictions) {
			PBSolver solver = new SAT4JPBSolver();
			solver.addRestrictions(baseRestrictions);
			solver.addRestrictions(restr.getInverse(idGen));
			
			if (solver.isSatisfiable()) {
				return false;
			}
		}		
		
		return true;
	}
	
	private static Set<String> getAddedFeatures(FeatureModel fm1, FeatureModel fm2) {
		Set<String> fm1Features = new HashSet<String>();
		for (String name : fm1.getFeatureNames()) {
			fm1Features.add(name);
		}
		Set<String> fm2Features = new HashSet<String>();
		for (String name : fm2.getFeatureNames()) {
			fm2Features.add(name);
		}
		
		fm2Features.removeAll(fm1Features);
		return fm2Features;
	}
}
