package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.BiMap;
import com.google.common.collect.Multimap;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;

public class BooleanConstraintPropagator implements AssignmentRegistry {

	private Collection<AeRestriction> restrictions;

	private FeatureModel fm;
	
	private BiMap<String, Integer> map;
	
	private Assignments assignments;
	
	private VarIdManager varIdManager;
	
	private Multimap<AeRestriction, Assignment> propagationQueue;
	
	public void setUp(Collection<AeRestriction> restrictions,
			FeatureModel fm, BiMap<String, Integer> map) {
		this.restrictions = restrictions;
		this.fm = fm;
		this.map = map;
		this.assignments = new Assignments();
		this.varIdManager = new VarIdManager();
		this.propagationQueue = ArrayListMultimap.create();
		setUpVarId2Restriction();
	}
	
	private void setUpVarId2Restriction() {
		for (AeRestriction restriction : restrictions) {
			for (Term term : restriction.getTerms()) {
				varIdManager.put(term.getId(), restriction);
			}
		}
	}
	
	public Assignments startPropagation(List<Feature> enabledFeatures, 
			List<Feature> disabledFeatures) throws ContradictionException {
		
		if (enabledFeatures != null) {
			for (Feature feature : enabledFeatures) {
				Assignment assignment = new Assignment(map.get(feature.getName()), true);
				reportAssignment(assignment);
			}
		}
		
		if (disabledFeatures != null) {
			for (Feature feature : disabledFeatures) {
				Assignment assignment = new Assignment(map.get(feature.getName()), true);
				reportAssignment(assignment);
			}
		}
		
		doBooleanConstraintPropagation();
		
		return assignments;
	}
	
	private void doBooleanConstraintPropagation() throws ContradictionException {
		while(propagationQueue.size() > 0) {
			AeRestriction restriction = propagationQueue.keys().iterator().next();
			 
			Collection<Assignment> assigns = propagationQueue.get(restriction);
			if (restriction.assign(assigns)) {
				varIdManager.remove(restriction);
			}
			propagationQueue.removeAll(restriction);
		}
	}

	@Override
	public void reportAssignment(Assignment assignment) {
		addAssignment(assignment);
		
		for (AeRestriction restriction : varIdManager.get(assignment.getId())) {
			propagationQueue.put(restriction, assignment);
		}
	}

	public void addAssignment(Assignment assignment) {
		Feature f = fm.getFeature(map.inverse().get(assignment.getId()));
		if (assignment.getAssignment()) {
			assignments.addPositiveAssignment(f);
		} else {
			assignments.addNegativeAssignment(f);
		}
	}
	
	
	private static class VarIdManager {
		
		private Multimap<Integer, AeRestriction> varId2Restriction;
		
		private Collection<AeRestriction> removedRestrictions;
		
		public VarIdManager() {
			this.varId2Restriction = ArrayListMultimap.create();
			this.removedRestrictions = new ArrayList<AeRestriction>();
		}
		
		public void put(int varId, AeRestriction restriction) {
			varId2Restriction.put(varId, restriction);
		}
		
		public Collection<AeRestriction> get(int varId) {
			Collection<AeRestriction> restrictions = varId2Restriction.get(varId);
			restrictions.removeAll(removedRestrictions);
			return restrictions;
		}
		
		public void remove(AeRestriction restriction) {
			removedRestrictions.remove(restriction);
		}
	}
}
