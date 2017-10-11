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
package de.ovgu.featureide.fm.core.base;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.impl.FeatureAttribute;
import de.ovgu.featureide.fm.core.base.impl.FeatureAttributeInherited;

/**
 * Manages all structural information of a feature.</br> Intended for tree structures (features are represented by tree nodes).
 *
 * @author Sebastian Krieter
 * @author Marcus Pinnecke
 */
public interface IFeatureStructure {

	void addChild(IFeatureStructure newChild);

	void addChildAtPosition(int index, IFeatureStructure newChild);

	void changeToAlternative();

	void changeToAnd();

	void changeToOr();

	IFeatureStructure cloneSubtree(IFeatureModel newFeatureModel);

	int getChildIndex(IFeatureStructure feature);

	List<IFeatureStructure> getChildren();	// Changed type LinkedList to List, Marcus Pinnecke 30.08.15

	LinkedList<FeatureAttributeInherited> getAttributeListInherited();

	LinkedList<FeatureAttribute> getAttributeList();

	int getChildrenCount();

	IFeature getFeature();

	IFeatureStructure getFirstChild();

	IFeatureStructure getLastChild();

	IFeatureStructure getParent();

	Collection<IConstraint> getRelevantConstraints();

	boolean hasChildren();

	boolean hasVisibleChildren(boolean showHiddenFeatures);

	boolean hasHiddenParent();

	boolean hasInlineRule();

	boolean isAbstract();

	boolean isAlternative();

	boolean isAncestorOf(IFeatureStructure next);

	boolean isAnd();

	boolean isANDPossible();

	boolean isConcrete();

	boolean isFirstChild(IFeatureStructure child);

	boolean isHidden();

	boolean isMandatory();

	boolean isMandatorySet();

	boolean isMultiple();

	boolean isOr();

	boolean isRoot();

	void removeChild(IFeatureStructure child);

	IFeatureStructure removeLastChild();

	void replaceChild(IFeatureStructure oldChild, IFeatureStructure newChild);

	void setAbstract(boolean value);

	void setAlternative();

	void setAnd();

	void setAND(boolean and);

	void setChildren(List<IFeatureStructure> children);	// Changed type LinkedList to List, Marcus Pinnecke 30.08.15

	void setHidden(boolean hid);

	void setMandatory(boolean mandatory);

	void setMultiple(boolean multiple);

	void setOr();

	void setParent(IFeatureStructure newParent);

	void setAttributeListInherited(LinkedList<FeatureAttributeInherited> attListRecursive);

	void setAttributeList(LinkedList<FeatureAttribute> attList);

	void setRelevantConstraints();

	void setRelevantConstraints(List<IConstraint> constraints); // Marcus, if calculated outside the class, see FeatureUtils.setRelevantConstraints(...)
}
