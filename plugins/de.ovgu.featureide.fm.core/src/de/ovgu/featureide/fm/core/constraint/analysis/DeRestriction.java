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
import java.util.List;

import de.ovgu.featureide.fm.core.constraint.RelationOperator;

/**
 * Implementation of the {@link Restriction} class.
 * 
 * @author Sebastian Henneberg
 */
public class DeRestriction extends Restriction {
	
	public DeRestriction(List<Term> terms, RelationOperator op, int degree) {
		super(terms, op, degree);
	}
	
	protected void init(List<Term> terms, RelationOperator op, int degree) {
		this.terms = makeDefensiveCopy(terms);
		this.op = op == RelationOperator.EQUAL ? Op.EQ : Op.GEQ;
		this.degree = degree;
		
		// if operator is "<=", multiply with (-1) to get ">="
		if (op == RelationOperator.LESS_EQUAL) {
			negateBothSides();
		}
		makeCoefficientsPositive();
		sortById();
	}
	
	public List<DeRestriction> getInverse(UniqueId idGen) {
		List<DeRestriction> inverseConjunction = new ArrayList<DeRestriction>();
		
		if (op == Op.GEQ) {
			// negated restriction for GEQ (>=):
			//     ~( +a_1*x_1 +a_2*x_2 ... >=  d)
			// <=> +a_1*x_1 +a_2*x_2 ...    <   d
			// <=> -a_1*x_1 -a_2*x_2 ...    >  -d
			// <=> -a_1*x_1 -a_2*x_2 ...    >= -d+1
			List<Term> newTerms = new ArrayList<Term>();
			for (Term term : terms) {
				newTerms.add(term.flipCoefficientSign());
			}
			inverseConjunction.add(new DeRestriction(
					newTerms, RelationOperator.GREATER_EQUAL, -degree+1));
		} else {
			// negated restriction for EQ (==):
			//     ~( +a_1*x_1 +a_2*x_2 ... ==  d)
			// <=> +a_1*x_1 +a_2*x_2 ...    !=  d
			// <=> (+a_1*x_1 +a_2*x_2 ...   >=  d+1) 
			//  || (+a_1*x_1 +a_2*x_2 ...   <=  d-1)
			// <=> (+a_1*x_1 +a_2*x_2 ...   >=  d+1)
			//  || (-a_1*x_1 -a_2*x_2 ...   >= -d+1)
			// <=> (+(d+1)y +a_1*x_1 +a_2*x_2 ... >= d+1) 
			//  && ((-d+1+a_1+a_2 ...)~y +a_1*x_1 +a_2*x_2 ... >= -d+1+a_1+a_2 ...)
			// <=> (+e y +a_1*x_1 +a_2*x_2 ... >= e) 
			//  && (+f~y +a_1*x_1 +a_2*x_2 ... >= f)
			// where e=d+1 and f=(-d+1+a_1+a_2 ...)
			List<Term> newTerms1 = new ArrayList<Term>();
			List<Term> newTerms2 = new ArrayList<Term>();
			int coefficientSum = 0;
			for (Term term : terms) {
				coefficientSum += term.getCoefficient();
				
				newTerms1.add(new Term(term));
				newTerms2.add(term.flipPositive());
			}
			int e = degree+1;
			int f = -degree+1+coefficientSum;
			
			int auxiliaryId = idGen.getNext();
			
			newTerms1.add(new Term(auxiliaryId, e, true));
			newTerms2.add(new Term(auxiliaryId, f, false));
			
			inverseConjunction.add(new DeRestriction(
					newTerms1, RelationOperator.GREATER_EQUAL, e));
			inverseConjunction.add(new DeRestriction(
					newTerms2, RelationOperator.GREATER_EQUAL, f));
		}
		
		return inverseConjunction;
	}
	
	@Override
	public boolean equals(Object object) {
		// same instance?
		if (this == object) return true;
		// different type?
		if (!(object instanceof DeRestriction)) return false;
		// depth equality check
		DeRestriction restriction = (DeRestriction) object;
		
		if (restriction.getDegree() != degree 
				|| restriction.getOp() != op
				|| restriction.getTerms().size() != terms.size()) return false;

		for (Term term : restriction.getTerms()) {
			if (!terms.contains(term))
				return false;
		}
		
		return true;
	}
	
	@Override
	public int hashCode() {
		int hashCode = 7 * degree;
		
		for (Term term : terms) {
			hashCode ^= term.hashCode();
		}
		
		hashCode ^= op == Op.GEQ ? 251 : 257 ; 
		
		return hashCode;
	}
}
