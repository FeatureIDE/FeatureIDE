/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.IRoleElement;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class SumImplementationArtifactsParent extends LazyParent {
	private FSTModel fstModel;

	private int type;

	public static final int NUMBER_OF_CLASSES = 0;
	public static final int NUMBER_OF_FIELDS = 1;
	public static final int NUMBER_OF_METHODS = 2;

	public SumImplementationArtifactsParent(String description, FSTModel fstModel, int type) {
		super(description);
		this.fstModel = fstModel;
		this.type = type;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	@Override
	protected void initChildren() {
		if (type == NUMBER_OF_CLASSES) {
			for (FSTClass currClass : fstModel.getClasses()) {
				for (LinkedList<FSTClassFragment> iterable_element : currClass.getAllFSTFragments()) {
					addChild(new ClassNodeParent(iterable_element.get(0).getFullIdentifier() + ": " + iterable_element.size(), iterable_element.get(0)));
				}
			}
		}
	}

}
