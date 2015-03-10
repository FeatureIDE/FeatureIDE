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

import java.util.ArrayList;
import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * TODO description
 * 
 * @author Schleicher Miro
 */
public class StatisticsProgramSizeNew extends LazyParent {

	private FSTModel fstModel;
	private int sumRoles;

	public StatisticsProgramSizeNew(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.ui.statistics.core.composite.LazyParent#initChildren()
	 */
	@Override
	protected void initChildren() {

		int pointer = 0;
		
//		ArrayList<FSTClassFragment> allClassesList = new ArrayList<FSTClassFragment>();
		
		int numberOfClasses = 0;
		int numberOfRoles = 0;
		int numberOfFields = 0;
		int numberOfMethods = 0;
		
		numberOfClasses = fstModel.getClasses().size();
		
		for (FSTClass class_ : fstModel.getClasses()) {
			//System.out.println();
			numberOfRoles += class_.getRoles().size();

			LinkedList<LinkedList<FSTClassFragment>> allFrag = class_.getAllFSTFragments();
			for (LinkedList<FSTClassFragment> linkedList : allFrag) {
				numberOfRoles += linkedList.size();
				for (FSTClassFragment fstClassFragment : linkedList) {
					numberOfMethods += fstClassFragment.getMethods().size();
					numberOfFields += fstClassFragment.getFields().size();
				}
			}
			numberOfClasses += allFrag.size();

		}


		addChild(new SumImplementationArtifactsParent("Number of classes: " + numberOfClasses + " Roles: " + numberOfRoles, fstModel, SumImplementationArtifactsParent.NUMBER_OF_CLASSES));
		addChild(new SumImplementationArtifactsParent("Number of fields: " + numberOfFields, fstModel, SumImplementationArtifactsParent.NUMBER_OF_FIELDS));
		addChild(new SumImplementationArtifactsParent("Number of methods: " + numberOfMethods, fstModel, SumImplementationArtifactsParent.NUMBER_OF_METHODS));
	}

}
