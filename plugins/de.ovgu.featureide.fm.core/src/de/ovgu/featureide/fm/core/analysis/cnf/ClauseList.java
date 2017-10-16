/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.analysis.cnf;

import java.util.ArrayList;
import java.util.Collection;

/**
 * Represents an instance of a satisfiability problem in CNF.
 *
 * @author Sebastian Krieter
 */
public class ClauseList extends ArrayList<LiteralSet> implements Cloneable {

	private static final long serialVersionUID = -4298323253677967328L;

	public ClauseList() {
		super();
	}

	public ClauseList(int size) {
		super(size);
	}

	public ClauseList(Collection<? extends LiteralSet> c) {
		super(c);
	}

	public ClauseList(ClauseList otherClauseList) {
		super(otherClauseList.size());
		for (final LiteralSet clause : otherClauseList) {
			this.add(clause.clone());
		}
	}

	@Override
	public ClauseList clone() {
		return new ClauseList(this);
	}

}
