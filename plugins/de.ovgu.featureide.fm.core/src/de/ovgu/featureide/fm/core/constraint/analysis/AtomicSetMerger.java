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

/**
 * TODO description
 */
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
