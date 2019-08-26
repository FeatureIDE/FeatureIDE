/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.attributes.formula;

import java.util.ArrayList;
import java.util.List;

import de.ovgu.featureide.fm.attributes.formula.formulas.AdditionFormula;
import de.ovgu.featureide.fm.attributes.formula.formulas.Constant;
import de.ovgu.featureide.fm.attributes.formula.formulas.KeyValueVariable;
import de.ovgu.featureide.fm.attributes.formula.formulas.ProductFormula;

/**
 * 
 * @author Chico Sundermann
 *
 */
public class KeyValueFormulaParser {

	public static AggregateFormula parseFormula(final String formulaString) throws FormulaSyntaxException {
		return new Object() {

			int index = -1;
			int currentChar;

			boolean eat(int charToEat) {
				while (currentChar == ' ') { // Skip spaces
					nextChar();
				}
				if (charToEat == currentChar) {
					nextChar();
					return true;
				}
				return false;

			}

			/**
			 * Go back to the last non space symbol or start of the string
			 */
			void spit() {
				while (index > 0 && (currentChar == ' ' || currentChar == -1)) {
					previousChar();
				}
			}

			boolean belongsToNumber(int c) {
				return c >= '0' && c <= '9' || c == '.';
			}

			void nextChar() {
				currentChar = (++index < formulaString.length()) ? formulaString.charAt(index) : -1;
			}

			void previousChar() {
				currentChar = (--index > 0) ? formulaString.charAt(index) : -2;
			}

			AggregateFormula getFormula() throws FormulaSyntaxException {
				nextChar();
				AggregateFormula formula = parseSummand();
				if (index < formulaString.length()) {
					throw new FormulaSyntaxException(index, currentChar);
				}
				return formula;
			}

			// Get constants, variables and subexpressions
			AggregateFormula parseFactor() throws FormulaSyntaxException {
				// TODO: handle negative variables/constants
				int startIndex = index;
				if (eat('"')) {
					startIndex = index;
					while (currentChar != '"' && currentChar != -1) {
						nextChar();
					}
					if (currentChar == -1) {
						spit();
						throw new FormulaSyntaxException(index, currentChar);
					}
					eat('"');
					return new KeyValueVariable(formulaString.substring(startIndex, index - 1));
				} else if (belongsToNumber(currentChar)) {
					while (belongsToNumber(currentChar)) {
						nextChar();
					}
					return new Constant(Double.parseDouble(formulaString.substring(startIndex, index)));
				} else if (eat('(')) {
					AggregateFormula expressionInBrackets = parseSummand();
					eat(')');
					return expressionInBrackets;
				}
				spit();
				throw new FormulaSyntaxException(index, currentChar);
			}

			AggregateFormula parseSummand() throws FormulaSyntaxException {
				List<AggregateFormula> summands = new ArrayList<>();
				List<Integer> signs = new ArrayList<>();
				summands.add(parseProduct()); // left side of sum
				signs.add(1);

				while (true) {
					if (eat(FormulaStringTable.ADD)) {
						summands.add(parseProduct());
						signs.add(1);
					} else if (eat(FormulaStringTable.SUBTRACT)) {
						summands.add(parseProduct());
						signs.add(-1);
					} else {
						return new AdditionFormula(summands, signs);
					}
				}

			}

			AggregateFormula parseProduct() throws FormulaSyntaxException {
				List<AggregateFormula> factors = new ArrayList<>();
				List<Integer> potencies = new ArrayList<>();
				factors.add(parseFactor());
				potencies.add(1);
				while (true) {
					if (eat('*')) {
						factors.add(parseFactor());
						potencies.add(1);
					} else if (eat('/')) {
						factors.add(parseFactor());
						potencies.add(-1);
					} else {
						return new ProductFormula(factors, potencies);
					}
				}

			}

		}.getFormula();
	}
}
