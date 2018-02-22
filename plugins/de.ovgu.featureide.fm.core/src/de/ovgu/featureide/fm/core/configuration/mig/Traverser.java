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
package de.ovgu.featureide.fm.core.configuration.mig;

import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.editing.cnf.Clause;

public class Traverser {
	private final boolean[] dfsMark;
	private final ModalImplicationGraph mig;

	private int[] model = null;

	public Traverser(ModalImplicationGraph adjList) {
		mig = adjList;
		dfsMark = new boolean[mig.getAdjList().size()];
	}

	public void setModel(int[] model) {
		this.model = model;
		Arrays.fill(dfsMark, false);
	}

	public void traverse(int curLiteral, Visitor<?> visitor) {
		traverse(curLiteral, visitor, true);
	}

	public void traverseStrong(int curLiteral, Visitor<?> visitor) {
		final Vertex vertex = mig.getVertex(curLiteral);

		// Strong Edges
		for (final int strongEdge : vertex.getStrongEdges()) {
			final int modelIndex = Math.abs(strongEdge) - 1;
			if (model[modelIndex] == 0) {
				model[modelIndex] = strongEdge;
				visitor.visitStrong(strongEdge);
			}
		}

		// Weak Edges
		final int[] complexClauses = vertex.getComplexClauses();
		final VecInt v = new VecInt();
		outerLoop: for (int i = 0; i < complexClauses.length; i++) {
			final Clause clause = mig.getComplexClauses().get(complexClauses[i]);

			v.clear();
			final int[] literals = clause.getLiterals();
			for (int j = 0; j < literals.length; j++) {
				final int literal = literals[j];
				if (literal == -curLiteral) {
					continue;
				}
				final int value = model[Math.abs(literal) - 1];

				if (value == 0) {
					// add literal to list
					if (v.size() >= 1) {
						continue outerLoop;
					}
					v.push(literal);
				} else {
					if (value == literal) {
						// Clause is satisfied
						continue outerLoop;
					} else {
						// Do nothing
					}
				}
			}

			if (v.size() == 1) {
				final int literal = v.get(0);
				final int modelIndex = Math.abs(literal) - 1;
				if (model[modelIndex] == 0) {
					model[modelIndex] = literal;
					visitor.visitStrong(literal);
					traverseStrong(literal, visitor);
				}
			}
		}
	}

	private void traverse(int curLiteral, Visitor<?> visitor, boolean strongPath) {
		final Vertex vertex = mig.getVertex(curLiteral);

		if (strongPath) {
			final int modelIndex = Math.abs(curLiteral) - 1;
			if (model[modelIndex] == 0) {
				model[modelIndex] = curLiteral;
				visitor.visitStrong(curLiteral);
			}
		}

		if (!dfsMark[vertex.getId()]) {
			dfsMark[vertex.getId()] = true;
			if (!strongPath) {
				visitor.visitWeak(curLiteral);
			}

			// Strong Edges
			for (final int strongEdge : vertex.getStrongEdges()) {
				if (model[Math.abs(strongEdge) - 1] == 0) {
					traverse(strongEdge, visitor, strongPath);
				}
			}

			final int[] complexClauses = vertex.getComplexClauses();

			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final Clause clause = mig.getComplexClauses().get(complexClauses[i]);

				v.clear();
				final int[] literals = clause.getLiterals();
				for (int j = 0; j < literals.length; j++) {
					final int literal = literals[j];
					if (literal == -curLiteral) {
						continue;
					}
					final int value = model[Math.abs(literal) - 1];

					if (value == 0) {
						// add literal to list
						v.push(literal);
					} else {
						if (value == literal) {
							// Clause is satisfied
							continue outerLoop;
						} else {
							// Do nothing
						}
					}
				}

				if (v.size() == 1) {
					final int literal = v.get(0);
					if (model[Math.abs(literal) - 1] == 0) {
						traverse(literal, visitor, strongPath);
					}
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						if (model[Math.abs(literal) - 1] == 0) {
							traverse(literal, visitor, false);
						}
					}
				}
			}
		}
	}

}
