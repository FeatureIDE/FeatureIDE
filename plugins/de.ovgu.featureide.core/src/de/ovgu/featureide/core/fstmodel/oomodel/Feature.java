/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
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
package de.ovgu.featureide.core.fstmodel.oomodel;

import java.util.TreeMap;

import de.ovgu.featureide.core.fstmodel.IClass;
import de.ovgu.featureide.core.fstmodel.IFSTModelElement;
import de.ovgu.featureide.core.fstmodel.IFeature;



/**
 * @author Constanze Adler
 * @author Tom Brosch
 * 
 */
public class Feature extends OOModelElement implements IFeature {
	
	private String name;
	
	public TreeMap<String, Class> classes;
	
	public Feature(String name) {
		this.name = name;
		classes = new TreeMap<String, Class>();
	}

	public String getName() {
		return name;
	}

	public IFSTModelElement[] getChildren() {
		if (classes == null) return null;
		IClass[] elements = new IClass[classes.size()];
		int i = 0;
		for (IClass c : classes.values())
			elements[i++] =  c;		
		return elements;
	}
}
