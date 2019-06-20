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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration.twise;

import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;

/**
 *
 * @author Sebastian Krieter
 */
public class PresenceCondition {

	private final TreeSet<Integer> groups = new TreeSet<>();

	private final ClauseList clauses;
	private int index;

	public PresenceCondition(ClauseList clauses) {
		this.clauses = clauses;
	}

	public void addGroup(int group) {
		groups.add(group);
	}

	public Set<Integer> getGroups() {
		return groups;
	}

	public ClauseList getClauses() {
		return clauses;
	}

	public int getIndex() {
		return index;
	}

	public void setIndex(int index) {
		this.index = index;
	}

	@Override
	public int hashCode() {
		return ((clauses == null) ? 0 : clauses.hashCode());
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if ((obj == null) || (getClass() != obj.getClass())) {
			return false;
		}
		return Objects.equals(clauses, ((PresenceCondition) obj).clauses);
	}

	@Override
	public String toString() {
		return "PresenceCondition [groups=" + groups + ", clauses=" + clauses + ", index=" + index + "]";
	}

}
