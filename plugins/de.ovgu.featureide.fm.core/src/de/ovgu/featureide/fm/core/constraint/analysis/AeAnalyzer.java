package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.List;

import com.google.common.collect.BiMap;

import de.ovgu.featureide.fm.core.ExtendedFeatureModel;
import de.ovgu.featureide.fm.core.Feature;

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
