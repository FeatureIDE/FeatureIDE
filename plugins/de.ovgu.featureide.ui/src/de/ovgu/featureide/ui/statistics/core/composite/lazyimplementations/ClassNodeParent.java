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
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Node to display the methods in the StatisticsProgrammSize
 * 
 * @author Schleicher Miro
 */
public class ClassNodeParent extends AbstractSortModeNode {

	FSTClass fstClass = null;
	FSTClassFragment fstClassFrag = null;
	FSTModel fstModel;

	public ClassNodeParent(String descString, FSTClass fstClass, FSTModel fstMod) {
		super(descString, fstClass.getRoles().size());
		this.fstClass = fstClass;
		this.fstModel = fstMod;

	}

	public ClassNodeParent(String descString, FSTClassFragment fstClassFrag, FSTModel fstMod) {
		super(descString);
		this.fstClassFrag = fstClassFrag;
		this.fstModel = fstMod;
	}


	@Override
	protected void initChildren() {

		if (fstClass != null) {

			for (FSTRole fstRole : fstClass.getRoles()) {
				addChild(new Parent(fstRole.getFeature().getName(), fstRole));
			}

		} else if (fstClassFrag != null) {

			for (FSTClass currClass : fstModel.getClasses()) {
				for (LinkedList<FSTClassFragment> iterable_element : currClass.getAllFSTFragments()) {
					for (FSTClassFragment fstFrag : iterable_element) {
						if (fstFrag.getFullIdentifier().equals(fstClassFrag.getFullIdentifier())) {
							addChild(new ClassSubNodeParent(fstFrag.getRole().getFeature().getName(), fstFrag));
						}
					}
				}
			}

		}


	}

}
