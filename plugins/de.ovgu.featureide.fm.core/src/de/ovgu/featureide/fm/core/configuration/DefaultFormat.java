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
package de.ovgu.featureide.fm.core.configuration;

import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.StringTokenizer;

import de.ovgu.featureide.fm.core.Feature;

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class DefaultFormat extends ConfigurationFormat {
	
	@Override
	public String readLine(String line) {
		if (line.startsWith("#") || line.isEmpty() || line.equals(" ")) {
			return null;
		}
		// the string tokenizer is used to also support the expression
		// format used by FeatureHouse
		StringTokenizer tokenizer = new StringTokenizer(line);
		LinkedList<String> hiddenFeatures = new LinkedList<String>();
		while (tokenizer.hasMoreTokens()) {
			String name = tokenizer.nextToken(" ");
			if (name.startsWith("\"")) {
				try {
					name = name.substring(1);
					name += tokenizer.nextToken("\"");
				} catch (NoSuchElementException e) {
					return "Feature '" + name + "' is corrupt. No ending quotation marks found.";
				} catch (NullPointerException e) {
					return "Feature '" + name + "' is corrupt. No ending quotation marks found.";
				}
				// Check for ending quotation mark
				try {
					String endingDelimiter = tokenizer.nextToken(" ");
					if (!endingDelimiter.startsWith("\"")) {
						return "Feature '" + name + "' is corrupt. No ending quotation marks found.";
					}
				} catch (Exception e) {
					return "Feature '" + name + "' is corrupt. No ending quotation marks found.";
				}
			}

			Feature feature = configuration.getFeatureModel().getFeature(name);
			if (feature != null && feature.hasHiddenParent()) {
				hiddenFeatures.add(name);
			} else {
				try {
					configuration.setManual(name, Selection.SELECTED);
				} catch (FeatureNotFoundException e) {
					return "Feature " + name + " does not exist";
				} catch (SelectionNotPossibleException e) {
					return "Feature " + name + " cannot be selected";
				}
			}
		}
		for (String name : hiddenFeatures) {
			try {
				configuration.setAutomatic(name, Selection.SELECTED);
			} catch (FeatureNotFoundException e) {
				return "Feature " + name + " does not exist";
			} catch (SelectionNotPossibleException e) {
				return "Feature " + name + " cannot be selected";
			}
		}
		return null;
	}
	
	@Override
	public void write() {
		
	}

}
