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

import java.util.HashSet;
import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a
 * given {@link FSTModel}.<br>
 * This node should only be used for a feature oriented project.
 * 
 * @author Schleicher Miro
 */
public class StatisticsProgramSizeNew extends LazyParent {

	private final FSTModel fstModel;

	public StatisticsProgramSizeNew(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {
		int numberOfClasses = 0;
		int numberOfRoles = 0;
		int numberOfFields = 0;
		int numberOfUniFields = 0;
		int numberOfMethods = 0;
		int numberOfUniMethods = 0;

		for (FSTClass fstClass : fstModel.getClasses()) {
			final LinkedList<LinkedList<FSTClassFragment>> allFrag = fstClass.getAllFSTFragments();
			final HashSet<FSTMethod> methHelper = new HashSet<FSTMethod>();
			final HashSet<FSTField> fieldHelper = new HashSet<FSTField>();

			for (LinkedList<FSTClassFragment> linkedList : allFrag) {
				numberOfRoles += linkedList.size();

				for (FSTClassFragment fstClassFragment : linkedList) {
					methHelper.addAll(fstClassFragment.getMethods());
					fieldHelper.addAll(fstClassFragment.getFields());

					numberOfMethods += fstClassFragment.getMethods().size();
					numberOfFields += fstClassFragment.getFields().size();
				}
			}

			numberOfUniFields += fieldHelper.size();
			numberOfUniMethods += methHelper.size();
			numberOfClasses += allFrag.size();
		}

		addChild(new SumImplementationArtifactsParent(NUMBER_CLASS + SEPARATOR + numberOfClasses + " | " + NUMBER_ROLE + SEPARATOR + numberOfRoles, fstModel,
				SumImplementationArtifactsParent.NUMBER_OF_CLASSES));
		addChild(new SumImplementationArtifactsParent(NUMBER_FIELD_U + SEPARATOR + numberOfUniFields + " | " + NUMBER_FIELD + SEPARATOR + numberOfFields,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_FIELDS));
		addChild(new SumImplementationArtifactsParent(NUMBER_METHOD_U + SEPARATOR + numberOfUniMethods + " | " + NUMBER_METHOD + SEPARATOR + numberOfMethods,
				fstModel, SumImplementationArtifactsParent.NUMBER_OF_METHODS));
	}

}
