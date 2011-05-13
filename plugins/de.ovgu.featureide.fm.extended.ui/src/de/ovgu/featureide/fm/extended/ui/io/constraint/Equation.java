package de.ovgu.featureide.fm.extended.ui.io.constraint;

import de.ovgu.featureide.fm.extended.ui.io.constraint.RelationOperator;

import java.util.List;


public class Equation {

	private List<WeightedTerm> weightedTerms;
	
	private RelationOperator operator;
	
	private int degree;

	public Equation(List<WeightedTerm> weightedTerms, String operator,
			int degree) {
		super();
		this.weightedTerms = weightedTerms;
		this.operator = RelationOperator.parseOperator(operator);
		this.degree = degree;
	}

	public List<WeightedTerm> getWeightedTerms() {
		return weightedTerms;
	}

	public RelationOperator getOperator() {
		return operator;
	}

	public int getDegree() {
		return degree;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (WeightedTerm term : weightedTerms) {
			sb.append(term.toString() + " ");
		}
		sb.append(operator.toString() + " ");
		sb.append(degree);
		return sb.toString();
	}
}
