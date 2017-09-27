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
package de.ovgu.featureide.featurehouse.meta.featuremodel;

/**
 * Defines the content of the feature model class.
 *
 * @author Jens Meinicke
 */
public interface IFeatureModelClass {

	static final String IMPORT_JPF = "import gov.nasa.jpf.vm.Verify;\r\n\r\n";
	static final String VALID =
		"/**\r\n\t * This formula represents the validity of the current feature selection.\r\n\t */\r\n\tpublic /*@pure@*/ static boolean valid() {\r\n\t\t";

	/**
	 * @return The required imports.
	 */
	String getImports();

	/**
	 * @return The class and the description.
	 */
	String getHead();

	/**
	 *
	 * @return The field definitions.
	 */
	String getFeatureFields();

	/**
	 *
	 * @return The formula that represents the feature model.
	 */
	String getFormula();

	/**
	 *
	 * @return Methods to get the selection of the field.
	 */
	String getGetter();

	/**
	 *
	 * @return A method that returns the current selection.
	 */
	String getSelection();

}
