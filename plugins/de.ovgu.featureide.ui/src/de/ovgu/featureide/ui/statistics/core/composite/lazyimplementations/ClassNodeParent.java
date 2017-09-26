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
package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;

import java.util.List;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.AbstractSortModeNode;

/**
 * Node to display the methods in the StatisticsProgrammSize
 *
 * @author Schleicher Miro
 */
public class ClassNodeParent extends AbstractSortModeNode {

	private final FSTModel fstModel;

	private FSTClass fstClass;
	private FSTClassFragment fstClassFrag;

	public ClassNodeParent(String descString, FSTClass fstClass, FSTModel fstMod) {
		super(descString, fstClass.getRoles().size());
		this.fstClass = fstClass;
		fstModel = fstMod;

	}

	public ClassNodeParent(String descString, FSTClassFragment fstClassFrag, FSTModel fstMod) {
		super(descString);
		this.fstClassFrag = fstClassFrag;
		fstModel = fstMod;
	}

	@Override
	protected void initChildren() {
		if (fstClass != null) {
			for (final FSTRole fstRole : fstClass.getRoles()) {
				addChild(new Parent(fstRole.getFeature().getName(), fstRole));
			}
		} else if (fstClassFrag != null) {

			for (final FSTClass currClass : fstModel.getClasses()) {
				for (final List<FSTClassFragment> classFragmentList : currClass.getAllFSTFragments()) {
					for (final FSTClassFragment fstFrag : classFragmentList) {
						if (fstFrag.getFullIdentifier().equals(fstClassFrag.getFullIdentifier())) {
							addChild(new ClassSubNodeParent(fstFrag.getRole().getFeature().getName(), fstFrag));
						}
					}
				}
			}
		}
	}

}
