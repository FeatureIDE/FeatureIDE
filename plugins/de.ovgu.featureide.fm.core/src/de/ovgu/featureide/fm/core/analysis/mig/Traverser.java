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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.sat4j.core.VecInt;
import org.sat4j.specs.IteratorInt;

import de.ovgu.featureide.fm.core.analysis.cnf.LiteralSet;

public class Traverser extends ATraverser {

	public Traverser(ModalImplicationGraph mig) {
		super(mig);
	}

	@Override
	public void traverse(int... curLiterals) {
		final HashMap<Integer, VecInt> complexClauseMap = new HashMap<>();
		Arrays.fill(dfsMark, false);

		traverseStrong(complexClauseMap, curLiterals);
		mainLoop: while (true) {
			for (final Iterator<Entry<Integer, VecInt>> entryIterator = complexClauseMap.entrySet().iterator(); entryIterator.hasNext();) {
				final Entry<Integer, VecInt> entry = entryIterator.next();
				final VecInt v = entry.getValue();
				if (v != null) {
					for (final IteratorInt iterator = v.iterator(); iterator.hasNext();) {
						final int literal = iterator.next();
						if (model[Math.abs(literal) - 1] == 0) {
							final Vertex vertex = mig.getVertex(literal);
							if (!dfsMark[vertex.getId()]) {
								dfsMark[vertex.getId()] = true;
								boolean changed = false;
								if (visitor.visitWeak(literal)) {
									changed |= attemptStrongSelect(literal, complexClauseMap);
								} else {
									changed |= addComplexClauses(complexClauseMap, vertex) > 0;
								}
								changed |= processComplexClauses(complexClauseMap);
								if (changed) {
									continue mainLoop;
								}
							}
						}
					}
				}
			}
			break;
		}
	}

	@Override
	public void traverseStrong(int... curLiterals) {
		traverseStrong(new HashMap<Integer, VecInt>(), curLiterals);
	}

	private void traverseStrong(final HashMap<Integer, VecInt> complexClauseMap, int... curLiterals) {
		boolean changed = false;
		for (final int curLiteral : curLiterals) {
			changed |= attemptStrongSelect(curLiteral, complexClauseMap);
		}
		if (changed) {
			processComplexClauses(complexClauseMap);
		}
	}

	private boolean processComplexClauses(final HashMap<Integer, VecInt> complexClauseMap) {
		boolean changedInLoop, changed = false;
		do {
			changedInLoop = false;
			final List<VecInt> unitClauses = new LinkedList<>();
			for (final Entry<Integer, VecInt> entry : complexClauseMap.entrySet()) {
				final VecInt v = entry.getValue();
				if (v != null) {
					for (int j = v.size() - 1; j >= 0; j--) {
						final int literal = v.get(j);
						final int value = model[Math.abs(literal) - 1];
						if (value != 0) {
							if (value == literal) {
								entry.setValue(null);
							} else {
								v.delete(j);
							}
							changed = true;
						}
					}

					if (v.size() == 1) {
						entry.setValue(null);
						unitClauses.add(v);
					}
				}
			}

			for (final VecInt v : unitClauses) {
				changedInLoop |= attemptStrongSelect(v.get(0), complexClauseMap);
			}
			changed |= changedInLoop;
		} while (changedInLoop);
		return changed;
	}

	private boolean attemptStrongSelect(final int curLiteral, final HashMap<Integer, VecInt> complexClauseMap) {
		final int modelIndex = Math.abs(curLiteral) - 1;
		if (model[modelIndex] == 0) {
			model[modelIndex] = curLiteral;
			visitor.visitStrong(curLiteral);
			final Vertex curVertex = mig.getVertex(curLiteral);
			if (complexClauseMap != null) {
				addComplexClauses(complexClauseMap, curVertex);
			}
			for (final int strongEdge : curVertex.getStrongEdges()) {
				final int modelIndex2 = Math.abs(strongEdge) - 1;
				if (model[modelIndex2] == 0) {
					model[modelIndex2] = strongEdge;
					visitor.visitStrong(strongEdge);
					if (complexClauseMap != null) {
						addComplexClauses(complexClauseMap, mig.getVertex(strongEdge));
					}
				}
			}
			if (complexClauseMap != null) {
				return false;
			}
			return true;
		}
		return false;
	}

	private int addComplexClauses(final HashMap<Integer, VecInt> complexClauseMap, final Vertex vertex) {
		int added = 0;
		final int[] complexClauses = vertex.getComplexClauses();
		for (int i = 0; i < complexClauses.length; i++) {
			final Integer index = complexClauses[i];
			if (!complexClauseMap.containsKey(index)) {
				final LiteralSet clause = mig.getComplexClauses().get(index);
				complexClauseMap.putIfAbsent(index, new VecInt(Arrays.copyOf(clause.getLiterals(), clause.size())));
				added++;
			}
		}
		return added;
	}

}
