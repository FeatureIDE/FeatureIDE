/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
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
