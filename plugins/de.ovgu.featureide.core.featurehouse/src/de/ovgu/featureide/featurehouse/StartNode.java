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
package de.ovgu.featureide.featurehouse;

/**
 * for determining the start node
 * 
 * @author Janet Feigenspan
 */
public class StartNode {
	/**
	 * describes the first node after the root
	 */
	private static String startNode;
	private static String [][] language = {{"java", "ClassDeclaration"}, 
								{"haskell", "module"}, {"c#", "class_declaration"},
								{"c", "Sequence_CodeUnit_TopLevel"}, {"javaCC", ""},
								{"xml", "XMI-File"}};
	
	/**
	 * sets the start node according to the language lang
	 * @param lang the language of the project. Currntly supported: Java,
	 * Haskell, C#, C, Xml
	 * @return the start node or <code> null </code>, if it could not be obtained
	 */
	public static String determineStartNode(String lang) {
		for (int i = 0; i < language.length; i++) {
			if (language[i][0].equalsIgnoreCase(lang)) {
				startNode = language[i][1];
				return startNode;
			}
		}
		return null;
	}
}
