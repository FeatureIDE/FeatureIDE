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

import java.math.BigInteger;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.pb.IPBSolver;
import org.sat4j.pb.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.constraint.analysis.Restriction.Op;

/**
 * Implementation of {@link PBSolver} using the sat4j library.
 * 
 * @author Sebastian Henneberg
 */
public class SAT4JPBSolver implements PBSolver {

	IPBSolver solver;
	
	boolean alreadyContradiction;
	
	public SAT4JPBSolver() {
		solver = SolverFactory.newDefault();
		alreadyContradiction = false;
	}
	
	@Override
	public <T extends Restriction> void addRestriction(T restriction) {
		IVecInt ids = new VecInt(restriction.getIds());
		Vec<BigInteger> coefficients = 
			new Vec<BigInteger>(restriction.getCoefficients());
		BigInteger degree = BigInteger.valueOf(restriction.getDegree());
		
		try {
			// add the inequality "terms >= degree"
			solver.addPseudoBoolean(ids, coefficients, true, degree);
			
			// add the inequality "terms <= degree" if the operator is EQ
			if (restriction.getOp() == Op.EQ) {
				solver.addPseudoBoolean(ids, coefficients, false, degree);
			}
		} catch (ContradictionException e) {
			alreadyContradiction = true;
		}
	}
	
	@Override
	public <T extends Restriction> void addRestrictions(
			Collection<T> restrictions) {
		
		for (Restriction restriction : restrictions) {
			addRestriction(restriction);
		}
	}

	@Override
	public boolean isSatisfiable() {
		if (alreadyContradiction)
			return false;
		
		try {
			return solver.isSatisfiable();
		} catch (TimeoutException e) {
			throw new RuntimeException(e.getMessage());
		}
	}

	@Override
	public boolean isSatisfiable(int[] assumptions) {
		if (alreadyContradiction)
			return false;
		
		try {
			return solver.isSatisfiable(new VecInt(assumptions));
		} catch (TimeoutException e) {
			throw new RuntimeException(e.getMessage());
		}
	}
	
	public Set<Integer> backbone(Set<Integer> varibales) {
		Set<Integer> backbone = new HashSet<Integer>();
		
		for (Integer variable : varibales) {
			if (!isSatisfiable(new int[] {variable})) {
				backbone.add(-variable);
			} else if (!isSatisfiable(new int[] {-variable})) {
				backbone.add(variable);
			}
		}
		
		return backbone;
	}
}
