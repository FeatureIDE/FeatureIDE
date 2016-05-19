/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.conversion;

import java.util.LinkedList;
import java.util.List;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * TODO description
 * 
 * @author Alexander
 */
public class ComplexConstraintConverter {
	private static final IFeatureModelFactory factory = FMFactoryManager.getFactory();
	
	protected IFeatureModel fm;
	
	/**
	 * @param fm
	 * @return
	 */
	public IFeatureModel convert(IFeatureModel model, IConverterStrategy converter) {
		//check if model is valid
		if(model == null) {
			throw new IllegalArgumentException("Invalid feature model.");
		}
		
		if(converter == null) {
			throw new IllegalArgumentException("Invalid converter.");
		}
		
		//Work with a clone
		fm = model.clone();
		
		List<Node> nodes = new LinkedList<Node>();
		
		//TODO logic and preprocessing
		
		return converter.convert(fm, nodes, true);
	}
	
}
