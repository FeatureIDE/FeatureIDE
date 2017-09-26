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

import java.util.HashMap;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a given {@link FSTModel}.<br> This node should only be used for a feature oriented
 * project.
 *
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class StatisticsProgramSize extends LazyParent {

	private final FSTModel fstModel;

	/**
	 * Constructor for a {@code ProgrammSizeNode}.
	 *
	 * @param description description of the node shown in the view
	 * @param fstModel FSTModel for the calculation
	 */
	public StatisticsProgramSize(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {
		final HashMap<String, Integer> methodMap = new HashMap<String, Integer>();
		final HashMap<String, Integer> fieldMap = new HashMap<String, Integer>();
		final HashMap<String, Integer> classMap = new HashMap<String, Integer>();

		for (final FSTClass class_ : fstModel.getClasses()) {
			for (final FSTRole role : class_.getRoles()) {
				final FSTClassFragment classFragment = role.getClassFragment();
				final String packageName = classFragment.getPackage();
				final String qualifiedPackageName = (packageName == null) ? "(default package)" : packageName;

				final String roleName = classFragment.getName().endsWith(".java") ? classFragment.getName().substring(0, classFragment.getName().length() - 5)
					: classFragment.getName();
				final String qualifiedRoleName = qualifiedPackageName + "." + roleName;

				final String qualifier = qualifiedRoleName + ".";

				for (final FSTMethod method : classFragment.getMethods()) {
					addToMap(qualifier + method.getFullName(), methodMap);
				}
				for (final FSTField field : classFragment.getFields()) {
					addToMap(qualifier + field.getFullName(), fieldMap);
				}
				addToMap(qualifiedRoleName, classMap);
			}
		}

		addChild(new HashMapNode(NUMBER_CLASS + SEPARATOR + classMap.keySet().size() + " | " + NUMBER_ROLE + SEPARATOR + sum(classMap), null, classMap));
		addChild(new HashMapNode(NUMBER_FIELD_U + SEPARATOR + fieldMap.keySet().size() + " | " + NUMBER_FIELD + SEPARATOR + sum(fieldMap), null, fieldMap));
		addChild(
				new HashMapNode(NUMBER_METHOD_U + SEPARATOR + methodMap.keySet().size() + " | " + NUMBER_METHOD + SEPARATOR + sum(methodMap), null, methodMap));
	}

	private void addToMap(String name, HashMap<String, Integer> map) {
		map.put(name, map.containsKey(name) ? map.get(name) + 1 : 1);
	}

	private Integer sum(HashMap<String, Integer> input) {
		Integer sum = 0;
		for (final Integer value : input.values()) {
			sum += value;
		}
		return sum;
	}
}
