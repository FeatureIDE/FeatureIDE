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
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

/**
 * The abstract Restriction class provides a template to build specialized 
 * subclasses which represent a pseudo-boolean restriction (equation 
 * or inequality). 
 * 
 * @author Sebastian Henneberg
 */
abstract public class Restriction {

	/**
	 * The terms that contain unknowns (on the left side of the restriction).
	 */
	protected List<Term> terms;
	
	/**
	 * The operator of the restriction which is either EQ (=) rr GEQ (>=).
	 */
	protected Op op;
	
	/**
	 * The degree is a simple integer term (on the right side of the restriction).
	 */
	protected int degree;
	
	public Restriction(List<Term> terms, RelationOperator op, int degree) {
		init(terms, op, degree);
	}
	
	/**
	 * The only abstract method that is responsible to define the normal form
	 * and store the terms, the operator and the degree.
	 * 
	 * @param terms The terms that contain unknowns.
	 * @param op The operator of the restriction.
	 * @param degree The degree is a simple integer term.
	 */
	abstract protected void init(List<Term> terms, RelationOperator op, int degree);
	
	/**
	 * Returns an array of variable id's in the implementation-dependent order.
	 * 
	 * @return The id's in the implementation-dependent order.
	 * @category SAT4J representation 
	 */
	public int[] getIds() {
		int[] ids = new int[terms.size()]; 
		int i = 0;
		for (Term term : terms) {
			// SAT4J interprets negative ids as 'not id' 
			ids[i++] = term.isPositive() ? term.getId() : -term.getId();
		}
		return ids;
	}
	
	/**
	 * Returns an array of coefficients in the implementation-dependent order.
	 * 
	 * @return The coefficients in implementation-dependent order.
	 * @category SAT4J representation 
	 */
	public BigInteger[] getCoefficients() {
		BigInteger[] coefficients = new BigInteger[terms.size()];
		int i = 0;
		for (Term term : terms) {
			coefficients[i++] = BigInteger.valueOf(term.getCoefficient());
		}
		return coefficients;
	}
	
	/**
	 * Returns a collection of terms in the implementation-dependent order.
	 * 
	 * @return A collection of terms in the implementation-dependent order.
	 * @category generic access
	 */
	Collection<Term> getTerms() {
		return Collections.unmodifiableCollection(terms);
	}
	
	/**
	 * Returns the operator of the restriction (either == o >=).
	 * 
	 * @return The operator of the restriction (either EQ oder GEQ).
	 * @category generic access
	 */
	Op getOp() {
		return op;
	}
	
	/**
	 * Returns the degree of the restriction.
	 * 
	 * @return The degree of the restriction.
	 * @category generic access
	 */
	public int getDegree() {
		return degree;
	}

	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		for (Term term : terms) {
			sb.append(term.toString());
			sb.append(" ");
		}
		sb.append(op);
		sb.append(" ");
		sb.append(degree);
		
		return sb.toString();
	}
	
	// transform all terms to have a positive variable (e.g. -3~x=0 <=> 3x=3)
	protected void makeVarsPositive() {
		List<Term> positiveVars = new ArrayList<Term>(); 
		for (Term term : terms) {
			if (!term.isPositive()) {
				positiveVars.add(term.flipBoth());
				degree -= term.getCoefficient();
			} else {
				positiveVars.add(term);
			}
		}
		terms = positiveVars;
	}
	
	// transform all term to have a positive coefficient (e.g. -3x=0 <=> 3~x=3)
	protected void makeCoefficientsPositive() {
		List<Term> positiveTerms = new ArrayList<Term>(); 
		for (Term term : terms) {
			if (term.getCoefficient() < 0) {
				positiveTerms.add(term.flipBoth());
				degree -= term.getCoefficient();
			} else {
				positiveTerms.add(term);
			}
		}
		terms = positiveTerms;
	}
	
	protected void negateBothSides() {
		// negate the terms
		List<Term> negativedTerms = new ArrayList<Term>(); 
		for (Term term : terms) {
			negativedTerms.add(term.flipCoefficientSign());
		}
		terms = negativedTerms;
		// negate the degree
		degree = -degree;
	}
	
	protected void sortById() {
		Collections.sort(terms, new IdComparator());
	}

	protected void sortByCoefficient() {
		Collections.sort(terms, new CoefficientComparator());
	}
	
	protected static List<Term> makeDefensiveCopy(List<Term> terms) {
		List<Term> copy = new ArrayList<Term>();
		for (Term term : terms) {
			copy.add(new Term(term));
		}
		return copy;
	}
	
	/**
	 * The IdComparator can be used in subclasses to sort the terms by the id's.
	 * 
	 * @author Sebastian Henneberg
	 */
	static protected class IdComparator implements Comparator<Term> {
		@Override
		public int compare(Term term1, Term term2) {
			return term1.getId() - term2.getId();
		}
	}
	
	/**
	 * The CoefficientComparator can be used in subclasses to sort the terms 
	 * by absolute value of coefficients.
	 * 
	 * @author Sebastian Henneberg
	 */
	static protected class CoefficientComparator implements Comparator<Term> {
		@Override
		public int compare(Term term1, Term term2) {
			return term1.getCoefficient() - term2.getCoefficient();
		}
	}
	
	public static enum Op {
		EQ("="),
		GEQ(">=");
		
		private String symbol;
		
		private Op(String symbol) {
			this.symbol = symbol;
		}
		
		@Override
		public String toString() {
			return symbol;
		}
	}
}
