package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class AtomicSetMerger {

	private AtomicSets atomicSets;
	
	private List<AsRestriction> restrictions;
	
	private PBSolver solver;
	
	public AtomicSetMerger(AtomicSets atomicSets, List<AsRestriction> restrictions) {
		this.atomicSets = atomicSets;
		this.restrictions = restrictions;
		prepareSolver();
	}
	
	private void prepareSolver() {
		solver = new SAT4JPBSolver();
		solver.addRestrictions(restrictions);
	}
	
	public Result tryMerge(Set<Integer> vars) {
		// nothing to merge!
		if (vars.size() == 1)
			return new Result();
		
		
		for (Integer var : vars) {
			Set<Integer> toTest = new HashSet<Integer>(vars);
			toTest.remove(var);
			Set<Integer> trueVars = getTrueVars(var, toTest);
			if (trueVars.size() != toTest.size()) {
				Set<Integer> firstPartition = new HashSet<Integer>(trueVars);
				firstPartition.add(var);
				Set<Integer> secondPartition = new HashSet<Integer>(vars);
				secondPartition.removeAll(firstPartition);
				return new Result(firstPartition, secondPartition);					
			}
		}
		
		// each variable in var implies the selection of each other var in vars
		// => merge them together! 
		merge(vars);
		return new Result();
	}
	
	private Set<Integer> getTrueVars(int assumption, Set<Integer> vars) {
		Set<Integer> trueVars = new HashSet<Integer>();
		
		for (Integer var : vars) {
			if (!solver.isSatisfiable(new int[] {assumption, -var})) {
				trueVars.add(var);
			}
		}
		
		return trueVars;
	}
	
	
	private void merge(Set<Integer> vars) {
		// melt the atomic sets to a new compound one
		int mergedAsId = atomicSets.merge(vars).getId();
		
		// remove redundant equations and inequalities
		List<AsRestriction> toRemove = new ArrayList<AsRestriction>();
		for (AsRestriction restriction : restrictions) {
			if (restriction.simplify(vars, mergedAsId)) {
				toRemove.add(restriction);
			}
		}
		restrictions.removeAll(toRemove);
		
		// fill the solver with the simplified set of equations and inequalities
		prepareSolver();
	}
	
	
	static class Result {
		
		boolean successful;
		
		Set<Integer> firstPartition;
		Set<Integer> secondPartition;
		
		public Result() {
			this.successful = true;
		}
		
		public Result(Set<Integer> firstPartition, Set<Integer> secondPartition) {
			this.successful = false;
			this.firstPartition = firstPartition;
			this.secondPartition = secondPartition;
		}
		
		public boolean wasSuccessful() {
			return successful;
		}
		
		public Set<Integer> getFirstPartition() {
			return firstPartition;
		}
		
		public Set<Integer> getSecondPartition() {
			return secondPartition;
		}
	}
}
