/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2017  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
package org.prop4j.smt;

/**
 * Function represents the function that can be used to create first-order-logic expressions.
 *
 * @author Joshua Sprey
 */
public class Function extends Term {

	public static final String ADDITION = "addition";
	public static final String NEGATE = "negate";
	public static final String SUBSTRACT = "substract";
	public static final String MULTIPLY = "multiply";
	public static final String DIVISION = "division";
	public static final String MODULO = "modulo";

	public String type;
	public Term[] terms;

	/**
	 * @param var
	 */
	protected Function(String type, Term... terms) {
		super(null);
		this.type = type;
		this.terms = terms;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();

		if (type.equals("negate")) {
			builder.append("-");
		}
		for (int i = 0; i < terms.length; i++) {
			final Term term = terms[i];
			builder.append(term.toString());
			if (i < (terms.length - 1)) {
				builder.append(" ");
				builder.append(getFunctionTypeString());
				builder.append(" ");
			}
		}
		return builder.toString();
	}

	private String getFunctionTypeString() {
		switch (type) {
		case ADDITION:
			return "+";
		case SUBSTRACT:
			return "-";
		case DIVISION:
			return "/";
		case MODULO:
			return "*";
		case MULTIPLY:
			return "%";
		case NEGATE:
		default:
			return "";
		}
	}
	////////////////////////// Static functions to create function

	public static Function addition(Term termLeft, Term termRight) {
		return new Function(ADDITION, termLeft, termRight);
	}

	public static Function sum(Term... term) {
		return new Function(ADDITION, term);
	}

	public static Function substract(Term termLeft, Term termRight) {
		return new Function(SUBSTRACT, termLeft, termRight);
	}

	public static Function multiply(Term termLeft, Term termRight) {
		return new Function(MULTIPLY, termLeft, termRight);
	}

	public static Function divide(Term termLeft, Term termRight) {
		return new Function(DIVISION, termLeft, termRight);
	}

	public static Function modulo(Term termLeft, Term termRight) {
		return new Function(MODULO, termLeft, termRight);
	}

	public static Function negate(Term term) {
		return new Function(NEGATE, term);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.Term#hashCode()
	 */
	@Override
	public int hashCode() {
		return super.hashCode() + (type.hashCode() * 9);
	}

}
