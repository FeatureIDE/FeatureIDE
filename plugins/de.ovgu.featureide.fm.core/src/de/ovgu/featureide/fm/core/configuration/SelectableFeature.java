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
package de.ovgu.featureide.fm.core.configuration;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import javax.annotation.Nonnull;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IFeature;

/**
 * A representation of a selectable feature for the configuration process.
 *
 * @author Marcus Pinnecke (Feature Interface)
 */
public class SelectableFeature extends TreeElement {

	private Selection manual = Selection.UNDEFINED;

	private Selection automatic = Selection.UNDEFINED;

	private Selection recommended = Selection.UNDEFINED;

	private final IFeature feature;

	private int recommendationValue = -1;
	private Map<Integer, Node> openClauses = null;

	private String name;

	public SelectableFeature(IFeature feature) {
		this.feature = feature;
	}

	public Selection getSelection() {
		return automatic == Selection.UNDEFINED ? manual : automatic;
	}

	public Selection getManual() {
		return manual;
	}

	public void setManual(Selection manual) {
		if ((manual == Selection.UNDEFINED) || (automatic == Selection.UNDEFINED)) {
			this.manual = manual;
		} else if (manual != automatic) {
			throw new SelectionNotPossibleException(getName(), manual);
		}
	}

	public Selection getAutomatic() {
		return automatic;
	}

	public void setAutomatic(Selection automatic) {
		if ((automatic == Selection.UNDEFINED) || (manual == Selection.UNDEFINED) || (manual == automatic)) {
			this.automatic = automatic;
		} else {
			throw new AutomaticalSelectionNotPossibleException(feature.getName(), automatic);
		}
	}

	public String getName() {
		if (name != null) {
			return name;
		}
		return feature == null ? "" : feature.getName();
	}

	public IFeature getFeature() {
		return feature;
	}

	@Override
	public String toString() {
		return getName();
	}

	public void setName(String name) {
		this.name = name;
	}

	public Selection getRecommended() {
		return recommended;
	}

	public void setRecommended(Selection recommended) {
		this.recommended = recommended;
	}

	public int getRecommendationValue() {
		return recommendationValue;
	}

	public void setRecommendationValue(int recommendationValue) {
		this.recommendationValue = recommendationValue;
	}

	@Nonnull
	public Collection<Node> getOpenClauses() {
		if (openClauses == null) {
			return Collections.emptyList();
		}
		return openClauses.values();
	}

	public void addOpenClause(int index, Node openClause) {
		if (openClauses == null) {
			openClauses = new TreeMap<>();
		}
		openClauses.put(index, openClause);
	}

	public void clearOpenClauses() {
		openClauses = null;
	}

	@Nonnull
	public Set<Integer> getOpenClauseIndexes() {
		if (openClauses != null) {
			return openClauses.keySet();
		}
		return Collections.emptySet();
	}

}
