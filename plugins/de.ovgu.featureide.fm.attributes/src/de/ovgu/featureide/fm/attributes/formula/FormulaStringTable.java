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

public class FormulaStringTable {

	public final static int ADD = '+';
	public final static int SUBTRACT = '-';
	public final static int MULTIPLY = '*';
	public final static int DIVIDE = '/';

	public final static int OPEN_BRACKET = '(';
	public final static int CLOSE_BRACKET = ')';

	public final static int VARIABLE_IDENTIFIER = '"';

	public final static String MIN = "Min";
	public final static String MAX = "Max";
	public final static String SUM = "Sum";
	public final static String AVG = "Average";
	public final static String MEDIAN = "Median";

	public final static String MIN_DESC = "Computes the minimum of the underlying scores";
	public final static String MAX_DESC = "Computes the maximum of the underlying scores";
	public final static String SUM_DESC = "Computes the sum of the underlying scores";
	public final static String AVG_DESC = "Computes the average of the underlying scores";
	public final static String MEDIAN_DESC = "Computes the median of the underlying scores";

}
