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
import java.util.HashMap;

import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTModel;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.HashMapNode;
import de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations.genericdatatypes.MyHashNode;

/**
 * TreeNode who stores the number of classes, roles, fields and methods of a
 * given {@link FSTModel}.<br>
 * This node should only be used for a feature oriented project.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public class StatisticsProgramSize extends LazyParent {
	private FSTModel fstModel;

	/**
	 * Constructor for a {@code ProgrammSizeNode}.
	 * 
	 * @param description
	 *            description of the node shown in the view
	 * @param fstModel
	 *            FSTModel for the calculation
	 */
	public StatisticsProgramSize(String description, FSTModel fstModel) {
		super(description);
		this.fstModel = fstModel;
	}

	@Override
	protected void initChildren() {
		HashMap<String, Integer> methodMap = new HashMap<String, Integer>();
		HashMap<String, Integer> fieldMap = new HashMap<String, Integer>();
		HashMap<String, Integer> classMap = new HashMap<String, Integer>();
		
		ArrayList<Object> listOfClasses = new ArrayList<Object>();
		ArrayList<Object> listOfRoles = new ArrayList<Object>();
		
		
		ArrayList<FSTClassFragment> ourAllClassesList = new ArrayList<FSTClassFragment>();
		int pointer = 0;

		for (FSTClass class_ : fstModel.getClasses()) {
			for (FSTRole role : class_.getRoles()) {
				listOfRoles.add(role);
				FSTClassFragment classFragment = role.getClassFragment();
				String packageName = classFragment.getPackage();
				String qualifiedPackageName = (packageName == null) ? "(default package)" : packageName;
				String roleName = classFragment.getName().endsWith(".java") ? classFragment.getName().substring(0, classFragment.getName().length() - 5)
						: classFragment.getName();
				String qualifiedRoleName = qualifiedPackageName + "." + roleName.substring(roleName.lastIndexOf('/') + 1);
				for (FSTMethod method : classFragment.getMethods())
					addToMap(method.getFullIdentifier(), methodMap);
				for (FSTField field : classFragment.getFields())
					addToMap(field.getFullIdentifier(), fieldMap);
				ourAllClassesList.add(classFragment);
				//addToMap(qualifiedRoleName, classMap);
			}
			listOfClasses.add(class_);
		}

		while (pointer < ourAllClassesList.size()) {
			for (FSTClassFragment fragment : ourAllClassesList.get(pointer).getInnerClasses()) {
				ourAllClassesList.add(fragment);
				listOfClasses.add(fragment);
				//addToMap(fragment.getFullIdentifier(), classMap);

				for (FSTMethod method : fragment.getMethods())
					addToMap(fragment.getFullIdentifier() + "." + method.getFullName(), methodMap);

				for (FSTField field : fragment.getFields())
					addToMap(fragment.getFullIdentifier() + "." + field.getFullName(), fieldMap);
			}
			pointer++;
		}																																	//	TODO:	FALSCH
		addChild(new MyHashNode(NUMBER_CLASS + SEPARATOR + /*(classMap.keySet().size())*/ listOfClasses.size() + " | " + NUMBER_ROLE + SEPARATOR + listOfRoles.size(), listOfClasses));

//		addChild(new HashMapNode(NUMBER_FIELD_U + SEPARATOR + fieldMap.keySet().size() + " | " + NUMBER_FIELD + SEPARATOR + sum(fieldMap), fieldMap));
//		addChild(new HashMapNode(NUMBER_METHOD_U + SEPARATOR + methodMap.keySet().size() + " | " + NUMBER_METHOD + SEPARATOR + sum(methodMap), null, methodMap));
	}

	private void addToMap(String name, HashMap<String, Integer> map) {
		map.put(name, map.containsKey(name) ? map.get(name) + 1 : 1);
	}

	private Integer sum(HashMap<String, Integer> input) {
		Integer sum = 0;
		for (Integer value : input.values()) {
			sum += value;
		}
		return sum;
	}
}
