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
