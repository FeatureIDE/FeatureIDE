/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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

import java.util.Collection;
import java.util.Set;
import java.util.TreeSet;

import de.ovgu.featureide.fm.core.analysis.cnf.ClauseList;
import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

/**
 * Represents a presence condition as an expression.
 * 
 * @author Sebastian Krieter
 */
public class PresenceCondition extends ClauseList {

	private static final long serialVersionUID = 1L;

	private final TreeSet<Integer> groups = new TreeSet<>();

	public PresenceCondition() {
		super();
	}

	public PresenceCondition(ClauseList otherClauseList) {
		super(otherClauseList);
	}

	public PresenceCondition(Collection<? extends LiteralSet> c) {
		super(c);
	}

	public PresenceCondition(int size) {
		super(size);
	}

	public void addGroup(int group) {
		groups.add(group);
	}

	public Set<Integer> getGroups() {
		return groups;
	}

	@Override
	public String toString() {
		return "PresenceCondition [" + super.toString() + "]";
	}

}
