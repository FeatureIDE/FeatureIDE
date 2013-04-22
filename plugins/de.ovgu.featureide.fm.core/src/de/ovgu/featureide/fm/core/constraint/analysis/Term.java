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

/**
 * Term represents a mathematical term in a (linear) pseudo-boolean restriction.
 * The class describes terms like <code>a*x_id<code> where a is an integer 
 * unequal 0, and id an integer greater 0. Additionally, the value of the 
 * boolean variable <code>x_id<code> can be inverted.
 * 
 * @author Sebastian Henneberg
 */
public final class Term implements Cloneable {

	/**
	 * Identifies the unknown boolean variable.
	 */
	private int id;

	/**
	 * False if the unknown boolean variable is negated.
	 */
	private boolean positive;

	/**
	 * The coefficient of the term.
	 */
	private int coefficient;

	/**
	 * Creates a new linear term using the same state than the passed instance.
	 * 
	 * @param term Defines the state of the new object.
	 */
	public Term(Term term) {
		super();
		this.id = term.getId();
		this.positive = term.isPositive();
		this.coefficient = term.getCoefficient();
	}

	/**
	 * Creates a new linear term with specified id and coefficient.
	 * 
	 * @param id The unique identification of the unknown boolean variable.
	 * @param coefficient The coefficient of the term.
	 * @param positive False if the unknown boolean variable is negated.
	 */
	public Term(int id, int coefficient, boolean positive) {
		super();
		this.id = id;
		this.positive = positive;
		this.coefficient = coefficient;
	}

	/**
	 * @return The unique identification of the unknown boolean variable.
	 */
	public int getId() {
		return id;
	}

	/**
	 * @return False if the unknown boolean variable is negated. True otherwise.
	 */
	public boolean isPositive() {
		return positive;
	}

	/**
	 * @return The coefficient of the term.
	 */
	public int getCoefficient() {
		return coefficient;
	}

	/**
	 * Flips a positive coefficient to a negative and vice versa preserving the
	 * absolute value.
	 */
	Term flipCoefficientSign() {
		return new Term(id, -coefficient, positive);
	}

	/**
	 * Flips the boolean sign of the unknown pseudo-boolean variable.
	 */
	Term flipPositive() {
		return new Term(id, coefficient, !positive);
	}

	/**
	 * Converts the term to equivalent term with a positive coefficient. The
	 * return value has to be added to the other side of the restriction. This
	 * method helps to achieve a normal form.
	 * 
	 * @return The value that has to be added to the other side of the
	 *         restriction (equation or inequality).
	 */
	Term flipBoth() {
		return new Term(id, -coefficient, !positive);
	}

	@Override
	public String toString() {
		String sign = coefficient >= 0 ? "+" : "";
		String pos = !positive ? "~" : "";
		return String.format("%s%s%sx%s", sign, coefficient, pos, id);
	}

	@Override
	public boolean equals(Object object) {
		// same instance?
		if (this == object)
			return true;
		// different type?
		if (!(object instanceof Term))
			return false;
		// depth equality check
		Term term = (Term) object;
		return term.getId() == id && term.getCoefficient() == coefficient
				&& (term.isPositive() == positive);
	}

	@Override
	public int hashCode() {
		int hashCode = (id * 17) ^ coefficient;
		return positive ? hashCode + 1 : hashCode;
	}

	@Override
	protected Object clone() throws CloneNotSupportedException {
		Term clone = (Term) super.clone();
		clone.id = id;
		clone.positive = positive;
		clone.coefficient = coefficient;
		return clone;
	}
}
