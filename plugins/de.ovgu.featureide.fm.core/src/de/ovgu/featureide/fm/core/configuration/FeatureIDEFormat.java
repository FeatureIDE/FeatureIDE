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

/**
 * TODO description
 * 
 * @author Sebastian Krieter
 */
public class FeatureIDEFormat extends ConfigurationFormat {
	public static final String EXTENSION = "fideconf";
	
	private boolean orgPropagate = false;

	public void prepareRead(Configuration configuration) {
		super.prepareRead(configuration);
		orgPropagate = configuration.isPropagate();
		configuration.setPropagate(false);
		configuration.resetValues();
	}
	
	public void finishRead() {
		configuration.setPropagate(orgPropagate);
	}

	public String readLine(String line) {
		if (line.startsWith("#")) {
			return null;
		}
		line = line.trim();
		if (!line.isEmpty()) {
			Selection manual = Selection.UNDEFINED, automatic = Selection.UNDEFINED;
			try {
				switch (Integer.parseInt(line.substring(0, 1))) {
					case 0: manual = Selection.UNSELECTED; break;
					case 1: manual = Selection.SELECTED;
				}
				switch (Integer.parseInt(line.substring(1, 2))) {
					case 0: automatic = Selection.UNSELECTED; break;
					case 1: automatic = Selection.SELECTED;
				}
			} catch (NumberFormatException e) {
				return "Wrong configuration format";
			}
			
			final String name = line.substring(2);
			
			final SelectableFeature feature = configuration.getSelectablefeature(name);
			if (feature == null) {
				return "Feature " + name + " does not exist";
			} else {
				try {
					configuration.setManual(feature, manual);
					configuration.setAutomatic(feature, automatic);
				} catch (SelectionNotPossibleException e) {
					return "Selection not possible on feature " + name;
				}
			}
		}
		return null;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.fm.core.configuration.ConfigurationFormat#write()
	 */
	@Override
	public void write() {
		// TODO Auto-generated method stub
		
	}

}
