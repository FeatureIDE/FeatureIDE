package de.ovgu.featureide.fm.core.constraint.analysis;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

public class AeRestriction extends Restriction {

	private AssignmentRegistry registry;
	
	private int coefficientSum;
	
	private Map<Integer, Term> idMap;
	
	public AeRestriction(List<Term> terms, RelationOperator op, int degree) {
		super(terms, op, degree);
	}
	
	public AeRestriction(AssignmentRegistry registry, List<Term> terms, 
			RelationOperator op, int degree) {
		super(terms, op, degree);
		this.registry = registry;
	}

	@Override
	protected void init(List<Term> terms, RelationOperator op, int degree) {
		// AeRestrictions are always greater equal inequalities 
		// equality can not be transformed to greater equal
		if (op == RelationOperator.EQUAL)
			throw new IllegalArgumentException("Operator of AeRestriction can not be equal (==)");
		
		this.terms = makeDefensiveCopy(terms);
		this.op = Op.GEQ;
		this.degree = degree;
		
		// if operator is "<=", multiply with (-1) to get ">="
		if (op == RelationOperator.LESS_EQUAL) {
			negateBothSides();
		}
		makeCoefficientsPositive();
		sortByCoefficient();
		
		// provides quick access to the terms via their id
		idMap = new HashMap<Integer, Term>();
		coefficientSum = 0;
		for (Term term : this.terms) {
			idMap.put(term.getId(), term);
			coefficientSum += term.getCoefficient();
		}
	}
	
	public boolean assign(Collection<Assignment> assignments) throws ContradictionException {
		applyAssignments(assignments);
		
		if (!isSatisfiable()) {
			throw new ContradictionException();
		}
		
		checkImpliedAssignments();
		
		return isSatisfied();
	}
	
	private void applyAssignments(Collection<Assignment> assignments) {
		for (Assignment assignment : assignments) {
			applyAssignment(assignment);
		}
	}
	
	private void applyAssignment(Assignment assignment) {		
		Term term = idMap.get(assignment.getId());
		
		// adjust degree and coefficientSum according to the assignment
		if (term.isPositive() == assignment.getAssignment()) {
			degree -= term.getCoefficient();
		}
		coefficientSum -= term.getCoefficient();
		
		// remove the term from the restriction
		terms.remove(term);
		idMap.remove(assignment.getId());
	}
	
	private void checkImpliedAssignments() {
		while (terms.size() > 0 && coefficientSum - terms.get(0).getCoefficient() < degree) {
			Term term = terms.get(0);
			Assignment assignment = new Assignment(term.getId(), term.isPositive());
			registry.reportAssignment(assignment);
			applyAssignment(assignment);
		}
	}
	
	private boolean isSatisfiable() {
		return coefficientSum >= degree;
	}
	
	public boolean isSatisfied() {
		if (degree >= 0) {
			return true;
		}
		return false;
	}

	
}
