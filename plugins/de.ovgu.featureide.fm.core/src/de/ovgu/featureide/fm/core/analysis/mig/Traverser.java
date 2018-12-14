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
import de.ovgu.featureide.fm.core.analysis.mig.Visitor.VisitResult;

public class Traverser extends ATraverser {

	private static class CancelException extends Exception {
		private static final long serialVersionUID = 4872529212110156314L;
	}

	public Traverser(ModalImplicationGraph mig) {
		super(mig);
	}

	@Override
	public void traverse(int... curLiterals) {
		try {
			traverseAll(curLiterals);
		} catch (final CancelException e) {}
	}

	private void traverseAll(int... curLiterals) throws CancelException {
		final HashMap<Integer, VecInt> openClauseMap = new HashMap<>();
		Arrays.fill(dfsMark, false);

		traverseStrong(openClauseMap, curLiterals);
		mainLoop: while (true) {
			for (final Iterator<Entry<Integer, VecInt>> openClauseIterator = openClauseMap.entrySet().iterator(); openClauseIterator.hasNext();) {
				final VecInt openClause = openClauseIterator.next().getValue();
				if (openClause != null) {
					for (final IteratorInt literalIterator = openClause.iterator(); literalIterator.hasNext();) {
						final int literal = literalIterator.next();
						if (currentConfiguration[getIndex(literal)] == 0) {
							final Vertex vertex = mig.getVertex(literal);
							if (!dfsMark[vertex.getId()]) {
								dfsMark[vertex.getId()] = true;
								boolean changed = false;
								final VisitResult visitWeakResult = visitor.visitWeak(literal);
								switch (visitWeakResult) {
								case Cancel:
									return;
								case Continue:
									changed |= addComplexClauses(openClauseMap, vertex) > 0;
									break;
								case Select:
									changed |= attemptStrongSelect(literal, openClauseMap);
									break;
								case Skip:
									break;
								default:
									throw new AssertionError(visitWeakResult);
								}
								changed |= processComplexClauses(openClauseMap);
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
		try {
			traverseStrong(new HashMap<Integer, VecInt>(), curLiterals);
		} catch (final CancelException e) {}
	}

	private void traverseStrong(final HashMap<Integer, VecInt> complexClauseMap, int... curLiterals) throws CancelException {
		boolean changed = false;
		for (final int curLiteral : curLiterals) {
			changed |= attemptStrongSelect(curLiteral, complexClauseMap);
		}
		if (changed) {
			processComplexClauses(complexClauseMap);
		}
	}

	private boolean processComplexClauses(final HashMap<Integer, VecInt> complexClauseMap) throws CancelException {
		boolean changedInLoop, changed = false;
		do {
			changedInLoop = false;
			final List<VecInt> unitClauses = new LinkedList<>();
			for (final Entry<Integer, VecInt> entry : complexClauseMap.entrySet()) {
				final VecInt v = entry.getValue();
				if (v != null) {
					for (int j = v.size() - 1; j >= 0; j--) {
						final int literal = v.get(j);
						final int value = currentConfiguration[getIndex(literal)];
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

	private boolean attemptStrongSelect(final int curLiteral, final HashMap<Integer, VecInt> complexClauseMap) throws CancelException {
		final int modelIndex = getIndex(curLiteral);
		final int currentVariableSelection = currentConfiguration[modelIndex];
		if (currentVariableSelection == 0) {
			currentConfiguration[modelIndex] = curLiteral;
			VisitResult visitStrongResult = visitor.visitStrong(curLiteral);
			switch (visitStrongResult) {
			case Cancel:
				throw new CancelException();
			case Skip:
				return true;
			case Select:
			case Continue:
				break;
			default:
				throw new AssertionError(visitStrongResult);
			}

			final Vertex curVertex = mig.getVertex(curLiteral);
			addComplexClauses(complexClauseMap, curVertex);

			for (final int strongVertex : curVertex.getStrongEdges()) {
				final int strongVertexIndex = getIndex(strongVertex);
				if (currentConfiguration[strongVertexIndex] == 0) {
					currentConfiguration[strongVertexIndex] = strongVertex;
					visitStrongResult = visitor.visitStrong(strongVertex);
					switch (visitStrongResult) {
					case Cancel:
						throw new CancelException();
					case Skip:
						break;
					case Select:
					case Continue:
						addComplexClauses(complexClauseMap, mig.getVertex(strongVertex));
						break;
					default:
						throw new AssertionError(visitStrongResult);
					}
				}
			}
			return true;
		} else if (currentVariableSelection != curLiteral) {
			// TODO

		}
		return false;
	}

	private int getIndex(final int literal) {
		return Math.abs(literal) - 1;
	}

	private int addComplexClauses(final HashMap<Integer, VecInt> complexClauseMap, final Vertex vertex) {
		int added = 0;
		final int[] complexClauses = vertex.getComplexClauses();
		for (int i = 0; i < complexClauses.length; i++) {
			final Integer index = complexClauses[i];
			if (!complexClauseMap.containsKey(index)) {
				final LiteralSet clause = mig.getComplexClauses().get(index);
				complexClauseMap.put(index, new VecInt(Arrays.copyOf(clause.getLiterals(), clause.size())));
				added++;
			}
		}
		return added;
	}

//	@Override
//	public void traverseAll(int... curLiterals) {
//		final HashMap<Integer, VecInt> openClauseMap = new HashMap<>();
//		Arrays.fill(dfsMark, false);
//
//		traverseStrong(openClauseMap, curLiterals);
//		mainLoop: while (true) {
//			for (final Iterator<Entry<Integer, VecInt>> openClauseIterator = openClauseMap.entrySet().iterator(); openClauseIterator.hasNext();) {
//				final VecInt openClause = openClauseIterator.next().getValue();
//				if (openClause != null) {
//					for (final IteratorInt literalIterator = openClause.iterator(); literalIterator.hasNext();) {
//						final int literal = literalIterator.next();
//						if (currentConfiguration[getIndex(literal)] == 0) {
//							final Vertex vertex = mig.getVertex(literal);
//							if (!dfsMark[vertex.getId()]) {
//								dfsMark[vertex.getId()] = true;
//								boolean changed = false;
//								if (visitor.visitWeak(literal)) {
//									changed |= attemptStrongSelect(literal, openClauseMap);
//								} else {
//									changed |= addComplexClauses(openClauseMap, vertex) > 0;
//								}
//								changed |= processComplexClauses(openClauseMap);
//								if (changed) {
//									continue mainLoop;
//								}
//							}
//						}
//					}
//				}
//			}
//			break;
//		}
//	}
//
//	private boolean processComplexClauses(final HashMap<Integer, VecInt> complexClauseMap) {
//		boolean changedInLoop, changed = false;
//		do {
//			changedInLoop = false;
//			final List<VecInt> unitClauses = new LinkedList<>();
//			for (final Entry<Integer, VecInt> entry : complexClauseMap.entrySet()) {
//				final VecInt v = entry.getValue();
//				if (v != null) {
//					for (int j = v.size() - 1; j >= 0; j--) {
//						final int literal = v.get(j);
//						final int value = currentConfiguration[getIndex(literal)];
//						if (value != 0) {
//							if (value == literal) {
//								entry.setValue(null);
//							} else {
//								v.delete(j);
//							}
//							changed = true;
//						}
//					}
//
//					if (v.size() == 1) {
//						entry.setValue(null);
//						unitClauses.add(v);
//					}
//				}
//			}
//
//			for (final VecInt v : unitClauses) {
//				changedInLoop |= attemptStrongSelect2(v.get(0), complexClauseMap);
//			}
//			changed |= changedInLoop;
//		} while (changedInLoop);
//		return changed;
//	}
//
//	private boolean attemptStrongSelect(final int curLiteral, final HashMap<Integer, VecInt> complexClauseMap) {
//		final int modelIndex = getIndex(curLiteral);
//		if (currentConfiguration[modelIndex] == 0) {
//			currentConfiguration[modelIndex] = curLiteral;
//			visitor.visitStrong(curLiteral);
//			final Vertex curVertex = mig.getVertex(curLiteral);
//			if (complexClauseMap != null) {
//				addComplexClauses(complexClauseMap, curVertex);
//			}
//			for (final int strongVertex : curVertex.getStrongEdges()) {
//				final int strongVertexIndex = getIndex(strongVertex);
//				if (currentConfiguration[strongVertexIndex] == 0) {
//					currentConfiguration[strongVertexIndex] = strongVertex;
//					visitor.visitStrong(strongVertex);
//					if (complexClauseMap != null) {
//						addComplexClauses(complexClauseMap, mig.getVertex(strongVertex));
//					}
//				}
//			}
//			if (complexClauseMap != null) {
//				return false;
//			}
//			return true;
//		}
//		return false;
//	}

}
