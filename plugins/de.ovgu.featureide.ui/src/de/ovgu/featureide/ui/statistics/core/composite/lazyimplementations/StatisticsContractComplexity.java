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

import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECT_BASED__;

import java.util.HashMap;
import java.util.LinkedList;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;

/**
 * description
 *
 * @author Stefan Krueger
 * @author Florian Proksch
 */
public class StatisticsContractComplexity extends LazyParent {

	private final FSTModel fstModel;
	private final IFeatureModel featModel;
	private final String contractComposition;

	public StatisticsContractComplexity(String description, FSTModel fstmodel, IFeatureModel featmodel, String contractComposition) {
		super(description, null);
		fstModel = fstmodel;
		featModel = featmodel;
		this.contractComposition = contractComposition;
	}

	@Override
	protected void initChildren() {
		if (fstModel != null) {

			final HashMap<String, Integer> classInvariantsMap = new HashMap<String, Integer>();
			final HashMap<String, Integer> classMethodContractMap = new HashMap<String, Integer>();
			final HashMap<String, Integer> classMethodMap = new HashMap<String, Integer>();
			final HashMap<String, Integer> classMethodCountMap = new HashMap<String, Integer>();
			final HashMap<String, Integer> contractRefinementMap = new HashMap<String, Integer>();
			final HashMap<String, Integer> featureCountList = new HashMap<String, Integer>();

			int numInProject = 0, numInvariantsInProject = 0, numClassesWithContract = 0, numClassesWithInvariants = 0;
			for (final FSTClass class_ : fstModel.getClasses()) {
				int numInClass = 0, numInvariantsInClass = 0;

				final String packageName = (class_.getRoles().size() == 0) ? null : class_.getRoles().get(0).getClassFragment().getPackage();
				final String fullClassName = ((packageName == null) ? "(default package)" : packageName) + "."
					+ ((class_.getName().endsWith(".java")) ? class_.getName().substring(0, class_.getName().length() - 5) : class_.getName());

				for (final FSTRole role : class_.getRoles()) {
					for (@SuppressWarnings("unused")
					final FSTInvariant invariant : role.getClassFragment().getInvariants()) {
						numInvariantsInClass++;
						featureCountList.put(role.getFeature().getName(),
								featureCountList.containsKey(role.getFeature().getName()) ? featureCountList.get(role.getFeature().getName()) + 1 : 1);
					}
					for (final FSTMethod method : role.getClassFragment().getMethods()) {
						classMethodCountMap.put(fullClassName + "." + method.getFullName(), 1);
						if (method.hasContract()) {
							featureCountList.put(role.getFeature().getName(),
									featureCountList.containsKey(role.getFeature().getName()) ? featureCountList.get(role.getFeature().getName()) + 1 : 1);
							numInClass++;
							contractRefinementMap.put(method.getCompKey(),
									contractRefinementMap.containsKey(method.getCompKey()) ? (contractRefinementMap.get(method.getCompKey()) + 1) : 1);
							if (classMethodMap.get(fullClassName + "." + method.getFullName()) != null) {
								classMethodMap.put(fullClassName + "." + method.getFullName(),
										classMethodMap.get(fullClassName + "." + method.getFullName()) + 1);
							} else {
								classMethodMap.put(fullClassName + "." + method.getFullName(), 1);
							}
						}
					}
				}

				classMethodContractMap.put(fullClassName, numInClass);
				classInvariantsMap.put(fullClassName, numInvariantsInClass);

				numInvariantsInProject += numInvariantsInClass;
				numInProject += numInClass;
				numClassesWithContract += numInClass > 0 ? 1 : 0;
				numClassesWithInvariants += numInvariantsInClass > 0 ? 1 : 0;
			}

			final HashMapNode methodsNode =
				new HashMapNode(NUMBER_METHOD_METHOD_CONTRACT + SEPARATOR + classMethodMap.keySet().size() + "/" + classMethodCountMap.keySet().size() + " ("
					+ Math.round(100 * (classMethodMap.keySet().size() / (double) classMethodCountMap.keySet().size())) + "%)", null, classMethodMap);
			methodsNode.initChildren();
			for (final Parent p : methodsNode.getChildren()) {
				final LinkedList<String> featureChildList = new LinkedList<String>();

				for (final FSTClass class_ : fstModel.getClasses()) {

					final String packageName = (class_.getRoles().size() == 0) ? null : class_.getRoles().get(0).getClassFragment().getPackage();
					final String fullClassName = ((packageName == null) ? "(default package)" : packageName) + "."
						+ ((class_.getName().endsWith(".java")) ? class_.getName().substring(0, class_.getName().length() - 5) : class_.getName());

					for (final FSTRole role : class_.getRoles()) {

						for (final FSTMethod method : role.getClassFragment().getMethods()) {
							if (method.hasContract()) {

								if (p.getDescription().equals(fullClassName + "." + method.getFullName())) {
									featureChildList.add(role.getFeature().getName());

								}
							}
						}
					}
				}

				final LinkedList<String> featureOrderList = new LinkedList<String>(featModel.getFeatureOrderList());
				featureOrderList.retainAll(featureChildList);
				for (final String s : featureOrderList) {
					p.addChild(new Parent(s));
				}
			}

			addChild(new HashMapNode(
					NUMBER_PROJECT_INVARIANT + SEPARATOR + numInvariantsInProject + " | " + NUMBER_CLASS_INVARIANT + SEPARATOR + numClassesWithInvariants + "/"
						+ fstModel.getClasses().size() + " (" + Math.round(100 * (numClassesWithInvariants / (double) fstModel.getClasses().size())) + "%)",
					null, classInvariantsMap));
			addChild(new HashMapNode(
					NUMBER_PROJECT_METHOD_CONTRACT + SEPARATOR + numInProject + " | " + NUMBER_CLASS_METHOD_CONTRACT + SEPARATOR + numClassesWithContract + "/"
						+ fstModel.getClasses().size() + " (" + Math.round(100 * (numClassesWithContract / (double) fstModel.getClasses().size())) + "%)",
					null, classMethodContractMap));

			addChild(methodsNode);

			final HashMap<String, Integer> contractRefinementRealNameMap = new HashMap<String, Integer>();
			if (contractComposition.equals("Method-based Composition")) {
				for (final String refinement : contractRefinementMap.keySet()) {
					contractRefinementRealNameMap.put(REFINEMENT_COMPOSING_MECHANISM_MAPPING.get(refinement.trim()), contractRefinementMap.get(refinement));
				}
			} else {
				// contractRefinementRealNameMap.put(PROJECT_BASED__ +
				// contractComposition, contractRefinementMap.get(""));
				for (final String refinement : contractRefinementMap.keySet()) {
					contractRefinementRealNameMap.put(PROJECT_BASED__ + contractComposition,
							contractRefinementMap.get(refinement) + (contractRefinementRealNameMap.containsKey(PROJECT_BASED__ + contractComposition)
								? contractRefinementRealNameMap.get(PROJECT_BASED__ + contractComposition) : 0));
				}
			}
			addChild(new HashMapNode(METHOD_CONTRACT_REFINEMENT, null, contractRefinementRealNameMap));

			addChild(new HashMapNode(METHOD_CONTRACTS_FEATURE, null, featureCountList));
		}
	}
}
