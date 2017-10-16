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
package de.ovgu.featureide.fm.core.analysis.cnf.generator.configuration;

import java.util.ArrayDeque;
import java.util.Arrays;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.EmptyClauseException;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph;
import de.ovgu.featureide.fm.core.analysis.cnf.generator.ModalImplicationGraph.Vertex;

/**
 *
 * @author Sebastian Krieter
 */
public class IncrementalTraverser {

	public static final byte MARK_CALC_SELECT = 8;
	public static final byte MARK_CALC_DESELECT = 4;
	public static final byte MARK_AUTO_SELECT = 2;
	public static final byte MARK_AUTO_DESELECT = 1;
	public static final byte MARK_AUTO_SELECTION = MARK_AUTO_SELECT | MARK_AUTO_DESELECT;

	private static final byte MARK_POS_TRAVERSED = 32;
	private static final byte MARK_NEG_TRAVERSED = 16;

	private final ModalImplicationGraph graph;

	private byte[] computationMark;
	private boolean[] complexClauseSatisfiability;

	public IncrementalTraverser(ModalImplicationGraph graph) {
		this.graph = graph;
		computationMark = new byte[graph.getAdjList().size()];
		complexClauseSatisfiability = new boolean[graph.getComplexClauses().size()];
	}

	public void selectVariable(int literal) {
		markStrong(literal, changed);
		traverseStrong(literal, changed);
	}

	public void selectVariables(int... literals) {
		for (int i = 0; i < literals.length; i++) {
			final int var = literals[i];
			if (var != 0) {
				selectVariable(var, Math.abs(var) - 1);
			}
		}
	}

	final ArrayDeque<Integer> changed = new ArrayDeque<>();

	// public byte[] markConnected(int literal) {
	// for (int i = 0; i < computationMark.length; i++) {
	// computationMark[i] &= MARK_AUTO_SELECTION;
	// }
	// final byte[] copy = Arrays.copyOf(computationMark, computationMark.length);
	// final boolean[] copy2 = Arrays.copyOf(complexClauseSatisfiability, complexClauseSatisfiability.length);
	//
	// changed.clear();
	// changed.push(literal);
	// traverseStrong(literal, changed);
	//
	// while (!changed.isEmpty()) {
	// traverseWeak(changed.pop(), changed);
	// }
	// complexClauseSatisfiability = copy2;
	// final byte[] temp = computationMark;
	// computationMark = copy;
	// return temp;
	// }

	public byte[] markConnected(int... literals) {
		for (int i = 0; i < computationMark.length; i++) {
			computationMark[i] &= MARK_AUTO_SELECTION;
		}
		final byte[] copy = Arrays.copyOf(computationMark, computationMark.length);
		final boolean[] copy2 = Arrays.copyOf(complexClauseSatisfiability, complexClauseSatisfiability.length);

		changed.clear();
		for (final int literal : literals) {
			changed.push(literal);
			traverseStrong(literal, changed);
		}

		final byte[] temp = computationMark;
		try {
			while (!changed.isEmpty()) {
				traverseWeak(changed.pop(), changed);
			}
		} catch (final EmptyClauseException e) {
			return null;
		} finally {
			complexClauseSatisfiability = copy2;
			computationMark = copy;
		}
		return temp;
	}

	public byte[] markConnected2(int... literals) {
		for (int i = 0; i < computationMark.length; i++) {
			computationMark[i] &= MARK_AUTO_SELECTION;
		}
		final byte[] copy = Arrays.copyOf(computationMark, computationMark.length);
		final boolean[] copy2 = Arrays.copyOf(complexClauseSatisfiability, complexClauseSatisfiability.length);

		final byte[] temp = computationMark;
		try {
			for (final int b : literals) {
				traverseWeak2(b);
			}
		} catch (final EmptyClauseException e) {
			return null;
		} finally {
			complexClauseSatisfiability = copy2;
			computationMark = copy;
		}
		return temp;
	}

	public ArrayDeque<Integer> getStronglyConnected(int literal) {
		traverseStrong(literal, changed);
		return changed;
	}

	private void traverseStrong(int curVar, ArrayDeque<Integer> changed) {
		final int curIndex = Math.abs(curVar) - 1;

		final Vertex vertex = graph.getAdjList().get(curIndex);
		final int[] strongEdges = curVar > 0 ? vertex.posStrongEdges : vertex.negStrongEdges;

		// Strong Edges
		for (int i = 0; i < strongEdges.length; i++) {
			markStrong(strongEdges[i], changed);
		}
	}

	private void markStrong(final int literal, ArrayDeque<Integer> changed) {
		final int index = Math.abs(literal) - 1;
		final byte mark = computationMark[index];
		assert ((mark | (literal > 0 ? MARK_AUTO_SELECT : MARK_AUTO_DESELECT)) & MARK_AUTO_SELECTION) != MARK_AUTO_SELECTION;
		if ((literal > 0) && ((mark & MARK_AUTO_SELECT) == 0)) {
			changed.push(literal);
			selectVariable(literal, index);
		}
		if ((literal < 0) && ((mark & MARK_AUTO_DESELECT) == 0)) {
			changed.push(literal);
			selectVariable(literal, index);
		}
	}

	protected void selectVariable(final int literal, final int index) {
		if (literal > 0) {
			computationMark[index] |= MARK_AUTO_SELECT;
			for (final int i : graph.getAdjList().get(index).negComplexClauses) {
				complexClauseSatisfiability[i] = true;
			}
		} else {
			computationMark[index] |= MARK_AUTO_DESELECT;
			for (final int i : graph.getAdjList().get(index).posComplexClauses) {
				complexClauseSatisfiability[i] = true;
			}
		}
	}

	protected LiteralSet getComplexClause(final int clauseIndex) {
		return complexClauseSatisfiability[clauseIndex] ? null : graph.getComplexClauses().get(clauseIndex);
	}

	private void traverseWeak(int curVar, ArrayDeque<Integer> changed) throws EmptyClauseException {
		final int curIndex = Math.abs(curVar) - 1;
		final Vertex vertex = graph.getAdjList().get(curIndex);

		final int[] strongEdges;
		final int[] complexClauses;
		if (curVar > 0) {
			strongEdges = vertex.posStrongEdges;
			complexClauses = vertex.posComplexClauses;
		} else {
			strongEdges = vertex.negStrongEdges;
			complexClauses = vertex.negComplexClauses;
		}

		// Strong Edges
		for (int i = 0; i < strongEdges.length; i++) {
			markStrong(strongEdges[i], changed);
		}

		// Weak Edges
		final VecInt v = new VecInt();
		for (final int complexClause : complexClauses) {
			final LiteralSet clause = getComplexClause(complexClause);
			if (clause != null) {
				v.clear();
				for (final int literal : clause.getLiterals()) {
					final int index = Math.abs(literal) - 1;
					if ((index != curIndex) && ((computationMark[index] & MARK_AUTO_SELECTION) == 0)) {
						v.push(literal);
					}
				}

				// if list size == 1 -> strong edge
				if (v.isEmpty()) {
					throw new EmptyClauseException();
				} else if (v.size() == 1) {
					final int literal = v.get(0);
					markStrong(literal, changed);
					traverseStrong(literal, changed);
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						traverseWeakRec(iterator.next());
					}
				}
			}
		}
	}

	private void traverseWeak2(int curVar) throws EmptyClauseException {
		final int curIndex = Math.abs(curVar) - 1;
		final Vertex vertex = graph.getAdjList().get(curIndex);

		final int[] complexClauses;
		if (curVar > 0) {
			complexClauses = vertex.posComplexClauses;
		} else {
			complexClauses = vertex.negComplexClauses;
		}

		// Weak Edges
		final VecInt v = new VecInt();
		for (final int complexClause : complexClauses) {
			final LiteralSet clause = getComplexClause(complexClause);
			if (clause != null) {
				v.clear();
				for (final int literal : clause.getLiterals()) {
					final int index = Math.abs(literal) - 1;
					if ((index != curIndex) && ((computationMark[index] & MARK_AUTO_SELECTION) == 0)) {
						v.push(literal);
					}
				}

				// if list size == 1 -> strong edge
				if (v.isEmpty()) {
					throw new EmptyClauseException();
				} else if (v.size() == 1) {
					final int literal = v.get(0);
					markStrong(literal, changed);
					traverseStrong(literal, changed);
				} else {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						traverseWeakRec(iterator.next());
					}
				}
			}
		}
	}

	private void traverseWeakRec(int curVar) {
		final int curIndex = Math.abs(curVar) - 1;
		final Vertex vertex = graph.getAdjList().get(curIndex);

		final int[] strongEdges;
		final int[] complexClauses;
		if (curVar > 0) {
			if ((computationMark[curIndex] & MARK_POS_TRAVERSED) != 0) {
				return;
			}
			computationMark[curIndex] |= MARK_POS_TRAVERSED;
			computationMark[curIndex] |= MARK_CALC_SELECT;
			strongEdges = vertex.posStrongEdges;
			complexClauses = vertex.posComplexClauses;
		} else {
			if ((computationMark[curIndex] & MARK_NEG_TRAVERSED) != 0) {
				return;
			}
			computationMark[curIndex] |= MARK_NEG_TRAVERSED;
			computationMark[curIndex] |= MARK_CALC_DESELECT;
			strongEdges = vertex.negStrongEdges;
			complexClauses = vertex.negComplexClauses;
		}

		// TODO is this if statement correct?
		// if ((computationMark[curIndex] & MARK_AUTO_SELECTION) != 0) {
		// Strong Edges
		for (int i = 0; i < strongEdges.length; i++) {
			traverseWeakRec(strongEdges[i]);
		}
		// }

		// Weak Edges
		final VecInt v = new VecInt();
		for (final int complexClause : complexClauses) {
			final LiteralSet clause = getComplexClause(complexClause);
			if (clause != null) {
				v.clear();
				for (final int literal : clause.getLiterals()) {
					final int index = Math.abs(literal) - 1;
					if ((index != curIndex) && ((computationMark[index] & MARK_AUTO_SELECTION) == 0)) {
						v.push(literal);
					}
				}

				for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
					traverseWeakRec(iterator.next());
				}
			}
		}
	}

}
