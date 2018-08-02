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
package de.ovgu.featureide.fm.core.analysis.mig;

import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

public class RecursiveTraverser extends ATraverser {

	public RecursiveTraverser(ModalImplicationGraph mig) {
		super(mig);
	}

	@Override
	public void setModel(int[] model) {
		super.setModel(model);
		Arrays.fill(dfsMark, false);
	}

	@Override
	public void traverse(int... literals) {
		for (final int curLiteral : literals) {
			traverse(true, curLiteral);
		}
	}

	@Override
	public void traverseStrong(int... literals) {
		for (final int curLiteral : literals) {
			traverseStrongRec(curLiteral);
		}
	}

	private void traverseStrongRec(int curLiteral) {
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
			final LiteralSet clause = mig.getComplexClauses().get(complexClauses[i]);

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
					traverseStrongRec(literal);
				}
			}
		}
	}

	private void traverse(boolean strongPath, int curLiteral) {
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
					traverse(strongPath, strongEdge);
				}
			}

			final int[] complexClauses = vertex.getComplexClauses();

			// Weak Edges
			final VecInt v = new VecInt();
			outerLoop: for (int i = 0; i < complexClauses.length; i++) {
				final LiteralSet clause = mig.getComplexClauses().get(complexClauses[i]);

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
						traverse(strongPath, literal);
					}
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						if (model[Math.abs(literal) - 1] == 0) {
							traverse(false, literal);
						}
					}
				}
			}
		}
	}

}
