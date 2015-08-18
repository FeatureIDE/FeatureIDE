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
package de.ovgu.featureide.fm.core.base;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.FeatureConnection;

/**
 * Manages all structural information of a feature.</br>
 * Intended for tree structures (features are represented by tree nodes).
 * 
 * @author Sebastian Krieter
 */
public interface IFeatureStructure {

	void addChild(IFeature newChild);

	void addChildAtPosition(int index, IFeature newChild);

	void addTargetConnection(FeatureConnection connection);

	void changeToAlternative();

	void changeToAnd();

	void changeToOr();

	int getChildIndex(IFeature feature);

	LinkedList<IFeature> getChildren();

	int getChildrenCount();

	IFeature getFeature();

	IFeature getFirstChild();

	IFeature getLastChild();

	IFeature getParent();

	Collection<IConstraint> getRelevantConstraints();

	List<FeatureConnection> getSourceConnections();

	List<FeatureConnection> getTargetConnections();

	boolean hasChildren();

	boolean hasHiddenParent();

	boolean hasInlineRule();

	boolean isAbstract();

	boolean isAlternative();

	boolean isAncestorOf(IFeature next);

	boolean isAnd();

	boolean isANDPossible();

	boolean isConcrete();

	boolean isFirstChild(IFeature child);

	boolean isHidden();

	boolean isMandatory();

	boolean isMandatorySet();

	boolean isMultiple();

	boolean isOr();

	boolean isRoot();

	void removeChild(IFeature child);

	IFeature removeLastChild();

	boolean removeTargetConnection(FeatureConnection connection);

	void replaceChild(IFeature oldChild, IFeature newChild);

	void setAbstract(boolean value);

	void setAlternative();

	void setAnd();

	void setAND(boolean and);

	void setChildren(LinkedList<IFeature> children);

	void setHidden(boolean hid);

	void setMandatory(boolean mandatory);

	void setMultiple(boolean multiple);

	void setOr();

	void setParent(IFeature newParent);

	void setRelevantConstraints();

}
