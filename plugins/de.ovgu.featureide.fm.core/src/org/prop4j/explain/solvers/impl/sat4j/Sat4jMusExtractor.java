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
package org.prop4j.explain.solvers.impl.sat4j;

import java.util.LinkedHashSet;
import java.util.Set;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.xplain.Xplain;

/**
 * A MUS extractor using a Sat4J oracle.
 * 
 * @author Timo G&uuml;nther
 */
public class Sat4jMusExtractor extends Sat4jMutableSatSolver implements MusExtractor {
	/**
	 * Constructs a new instance of this class.
	 */
	protected Sat4jMusExtractor() {}
	
	@Override
	protected Xplain<ISolver> createOracle() {
		return new Xplain<ISolver>(super.createOracle());
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Xplain<ISolver> getOracle() {
		return (Xplain<ISolver>) super.getOracle();
	}
	
	@Override
	public Set<Node> getMinimalUnsatisfiableSubset() throws IllegalStateException {
		final Set<Integer> indexes = getMinimalUnsatisfiableSubsetIndexes();
		final Set<Node> mus = new LinkedHashSet<>(indexes.size());
		for (final int index : indexes) {
			mus.add(getClause(index));
		}
		return mus;
	}
	
	@Override
	public Set<Integer> getMinimalUnsatisfiableSubsetIndexes() throws IllegalStateException {
		if (isSatisfiable()) {
			throw new IllegalStateException("Problem is satisfiable");
		}
		final int[] indexes;
		try {
			indexes = getOracle().minimalExplanation();
		} catch (TimeoutException e) {
			throw new IllegalStateException(e);
		}
		final Set<Integer> set = new LinkedHashSet<>(indexes.length);
		for (final int index : indexes) {
			set.add(getClauseIndexFromIndex(index));
		}
		return set;
	}
}