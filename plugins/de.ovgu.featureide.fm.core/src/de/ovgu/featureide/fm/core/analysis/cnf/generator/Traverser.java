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
package de.ovgu.featureide.fm.core.analysis.cnf.generator;

import java.util.ArrayDeque;
import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph.Vertex;
import de.ovgu.featureide.fm.core.base.IModalImplicationGraph.ITraverser;

/**
 * Adjacency list implementation for a feature graph.
 * 
 * @author Sebastian Krieter
 */
public class Traverser implements ITraverser {

	private static final byte MARK_CALC_SELECT = 8;
	private static final byte MARK_CALC_DESELECT = 4;
	private static final byte MARK_AUTO_SELECT = 2;
	private static final byte MARK_AUTO_DESELECT = 1;
	private static final byte MARK_AUTO_SELECTION = MARK_AUTO_SELECT | MARK_AUTO_DESELECT;

	private static final byte MARK_POS_TRAVERSED = 32;
	private static final byte MARK_NEG_TRAVERSED = 16;

	private final ModalImplicationGraph graph;

	private final byte[] computationMark;

	public Traverser(ModalImplicationGraph graph) {
		this.graph = graph;
		this.computationMark = new byte[graph.adjList.size()];
	}

	@Override
	public LiteralSet getStronglyConnected(int startVar) {
		final Vertex vertex = graph.adjList.get(Math.abs(startVar) - 1);
		return new LiteralSet((startVar > 0) ? vertex.posStrongEdges : vertex.negStrongEdges);
	}

	@Override
	public LiteralSet getWeaklyConnected(int startVar) {
		Arrays.fill(computationMark, (byte) 0);
		computationMark[Math.abs(startVar) - 1] |= startVar > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT;

		ArrayDeque<Integer> changed = new ArrayDeque<>();
		changed.push(startVar);
		traverseStrong(startVar, changed);

		while (!changed.isEmpty()) {
			traverseWeak(changed.pop(), changed);
		}

		final VecInt variablesMarkedForSelection = getVariablesMarkedForSelection();
		return new LiteralSet(Arrays.copyOf(variablesMarkedForSelection.toArray(), variablesMarkedForSelection.size()));
	}

	@Override
	public VecInt getVariablesMarkedForSelection() {
		final VecInt vecInt = new VecInt();
		for (int i = 0; i < computationMark.length; i++) {
			if ((computationMark[i] & MARK_AUTO_SELECT) != 0) {
				vecInt.push((i + 1));
			}
			if ((computationMark[i] & MARK_AUTO_DESELECT) != 0) {
				vecInt.push(-(i + 1));
			}
		}
		return vecInt;
	}

	@Override
	public VecInt getVariablesMarkedForCalculation() {
		final VecInt vecInt = new VecInt();
		for (int i = 0; i < computationMark.length; i++) {
			final byte mark = computationMark[i];
			if ((mark & MARK_AUTO_SELECTION) == 0) {
				if ((mark & MARK_CALC_SELECT) != 0) {
					vecInt.push((i + 1));
				}
				if ((mark & MARK_CALC_DESELECT) != 0) {
					vecInt.push(-(i + 1));
				}
			}
		}
		return vecInt;
	}

	@Override
	public void markDefined(LiteralSet definedVars) {
		Arrays.fill(computationMark, (byte) 0);

		for (int i = 0; i < definedVars.size(); i++) {
			final int var = definedVars.getLiterals()[i];
			computationMark[Math.abs(var) - 1] |= var > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT;
		}

		ArrayDeque<Integer> changed = new ArrayDeque<>();
		for (int var : definedVars.getLiterals()) {
			changed.push(var);
		}
		for (int var : definedVars.getLiterals()) {
			traverseStrong(var, changed);
		}

		while (!changed.isEmpty()) {
			traverseWeak(changed.pop(), changed);
		}
	}

	@Override
	public void markUndefined(LiteralSet undefinedVars) {
		Arrays.fill(computationMark, (byte) 0);

		for (int var : undefinedVars.getLiterals()) {
			traverseWeakRec(var);
		}
	}

	@Override
	public void markDefinedAndUndefined(LiteralSet definedVars, LiteralSet undefinedVars) {
		Arrays.fill(computationMark, (byte) 0);

		for (int i = 0; i < definedVars.size(); i++) {
			final int var = definedVars.getLiterals()[i];
			computationMark[Math.abs(var) - 1] |= var > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT;
		}

		ArrayDeque<Integer> changed = new ArrayDeque<>();
		for (int var : definedVars.getLiterals()) {
			changed.push(var);
		}
		for (int var : definedVars.getLiterals()) {
			traverseStrong(var, changed);
		}

		while (!changed.isEmpty()) {
			traverseWeak(changed.pop(), changed);
		}

		for (int var : undefinedVars.getLiterals()) {
			traverseWeakRec(var);
		}
	}

	private void traverseWeak(int curVar, ArrayDeque<Integer> changed) {
		final int curIndex = Math.abs(curVar) - 1;

		final Vertex vertex = graph.adjList.get(curIndex);
		final int[] complexClauses = (curVar > 0) ? vertex.posComplexClauses : vertex.negComplexClauses;

		// Weak Edges
		final VecInt v = new VecInt();
		outerLoop: for (int i = 0; i < complexClauses.length; i++) {
			final LiteralSet clause = graph.complexClauses.get(complexClauses[i]);

			v.clear();
			final int[] literals = clause.getLiterals();
			for (int j = 0; j < literals.length; j++) {
				final int literal = literals[j];
				final int index = Math.abs(literal) - 1;
				if (index == curIndex) {
					continue;
				}
				final int value = computationMark[index] & MARK_AUTO_SELECTION;

				switch (value) {
				case 0:
					// add literal to list
					v.push(literal);
					break;
				case MARK_AUTO_SELECT:
					if (literal > 0) {
						// Clause is satisfied
						continue outerLoop;
					}
					break;
				case MARK_AUTO_DESELECT:
					if (literal < 0) {
						// Clause is satisfied
						continue outerLoop;
					}
					break;
				default:
					// Do nothing
					break;
				}
			}

			// if list size == 1 -> strong edge
			if (v.size() == 1) {
				final int literal = v.get(0);
				markStrong(literal, changed);
				traverseStrong(literal, changed);
			} else {
				for (IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					traverseWeakRec(iterator.next());
				}
			}
		}
	}

	private void traverseStrong(int curVar, ArrayDeque<Integer> changed) {
		final int curIndex = Math.abs(curVar) - 1;

		final Vertex vertex = graph.adjList.get(curIndex);
		final int[] strongEdges = curVar > 0 ? vertex.posStrongEdges : vertex.negStrongEdges;

		// Strong Edges
		for (int i = 0; i < strongEdges.length; i++) {
			markStrong(strongEdges[i], changed);
		}
	}

	private void markStrong(final int literal, ArrayDeque<Integer> changed) {
		final int index = Math.abs(literal) - 1;
		assert ((computationMark[index] | (literal > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT)) & MARK_AUTO_SELECTION) != MARK_AUTO_SELECTION;
		if ((computationMark[index] & MARK_AUTO_SELECTION) == 0) {
			computationMark[index] |= literal > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT;
			changed.push(literal);
		}
	}

	private void traverseWeakRec(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;
		if ((computationMark[curIndex] & MARK_AUTO_SELECTION) != 0) {
			return;
		}

		final int[] strongEdges;
		final int[] complexClauses;
		if (curVar > 0) {
			if ((computationMark[curIndex] & MARK_POS_TRAVERSED) != 0) {
				return;
			}
			computationMark[curIndex] |= MARK_POS_TRAVERSED;
			computationMark[curIndex] |= MARK_CALC_SELECT;
			final Vertex vertex = graph.adjList.get(curIndex);
			strongEdges = vertex.posStrongEdges;
			complexClauses = vertex.posComplexClauses;
		} else {
			if ((computationMark[curIndex] & MARK_NEG_TRAVERSED) != 0) {
				return;
			}
			computationMark[curIndex] |= MARK_NEG_TRAVERSED;
			computationMark[curIndex] |= MARK_CALC_DESELECT;
			final Vertex vertex = graph.adjList.get(curIndex);
			strongEdges = vertex.negStrongEdges;
			complexClauses = vertex.negComplexClauses;
		}

		// Strong Edges
		for (int i = 0; i < strongEdges.length; i++) {
			traverseWeakRec(strongEdges[i]);
		}

		// Weak Edges
		final VecInt v = new VecInt();
		outerLoop: for (int i = 0; i < complexClauses.length; i++) {
			final LiteralSet clause = graph.complexClauses.get(complexClauses[i]);

			v.clear();
			final int[] literals = clause.getLiterals();
			for (int j = 0; j < literals.length; j++) {
				final int literal = literals[j];
				final int index = Math.abs(literal) - 1;
				if (index == curIndex) {
					continue;
				}
				final int value = computationMark[index] & MARK_AUTO_SELECTION;

				switch (value) {
				case 0:
					// add literal to list
					v.push(literal);
					break;
				case MARK_AUTO_SELECT:
					if (literal > 0) {
						// Clause is satisfied
						continue outerLoop;
					}
					break;
				case MARK_AUTO_DESELECT:
					if (literal < 0) {
						// Clause is satisfied
						continue outerLoop;
					}
					break;
				default:
					// Do nothing
					break;
				}
			}

			for (IteratorInt iterator = v.iterator(); iterator.hasNext();) {
				traverseWeakRec(iterator.next());
			}
		}
	}

}