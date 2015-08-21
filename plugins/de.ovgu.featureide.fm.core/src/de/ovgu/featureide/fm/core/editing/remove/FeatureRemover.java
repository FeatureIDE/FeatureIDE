/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.core.editing.remove;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 * 
 * @author Sebastian Krieter
 */
public class FeatureRemover implements LongRunningMethod<Node> {

	private final Node fmNode;

	private final Collection<String> features;

	private final boolean includeBooleanValues;

	// all clauses that have both kinds of literals (remove AND retain)
	private List<DeprecatedClause> relevantClauseList;
	private Set<DeprecatedClause> relevantClauseSet;

	// list for all new construct clauses
	private Set<DeprecatedClause> newClauseSet;

	private DeprecatedFeatureMap map;

	public FeatureRemover(Node cnf, Collection<String> features) {
		this(cnf, features, true);
	}

	public FeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues) {
		this.fmNode = cnf;
		this.features = features;
		this.includeBooleanValues = includeBooleanValues;
	}

	private void addLiteral(HashSet<String> retainedFeatures, Node orChild) {
		final Literal literal = (Literal) orChild;
		if (literal.var instanceof String) {
			retainedFeatures.add((String) literal.var);
		}
	}

	public Node execute(WorkMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		final HashSet<String> retainedFeatures = new HashSet<>();
		if (fmNode instanceof And) {
			for (Node andChild : fmNode.getChildren()) {
				if (andChild instanceof Or) {
					for (Node orChild : andChild.getChildren()) {
						addLiteral(retainedFeatures, orChild);
					}
				} else {
					addLiteral(retainedFeatures, andChild);
				}
			}
		} else if (fmNode instanceof Or) {
			for (Node orChild : fmNode.getChildren()) {
				addLiteral(retainedFeatures, orChild);
			}
		} else {
			addLiteral(retainedFeatures, fmNode);
		}
		retainedFeatures.removeAll(features);

		if (fmNode instanceof And) {
			workMonitor.setMaxAbsoluteWork(features.size() + 2);

			final Node[] andChildren = fmNode.getChildren();

			relevantClauseList = new ArrayList<>(andChildren.length);
			relevantClauseSet = new HashSet<>(relevantClauseList);

			newClauseSet = new HashSet<>(andChildren.length);

			map = new DeprecatedFeatureMap(features);

			// fill first two lists
			for (int i = 0; i < andChildren.length; i++) {
				Node andChild = andChildren[i];

				final DeprecatedClause curClause;

				if (andChild instanceof Or) {
					int absoluteValueCount = 0;
					boolean valid = true;

					final Literal[] children = Arrays.copyOf(andChild.getChildren(), andChild.getChildren().length, Literal[].class);
					for (int j = 0; j < children.length; j++) {
						final Literal literal = children[j];

						// sort out obvious tautologies
						if (literal.var.equals(NodeCreator.varTrue)) {
							if (literal.positive) {
								valid = false;
							} else {
								absoluteValueCount++;
								children[j] = null;
							}
						} else if (literal.var.equals(NodeCreator.varFalse)) {
							if (literal.positive) {
								absoluteValueCount++;
								children[j] = null;
							} else {
								valid = false;
							}
						}
					}

					if (valid) {
						if (absoluteValueCount > 0) {
							if (children.length == absoluteValueCount) {
								throw new RuntimeException("Model is void!");
							}
							Literal[] newChildren = new Literal[children.length - absoluteValueCount];
							int k = 0;
							for (int j = 0; j < children.length; j++) {
								final Literal literal = children[j];
								if (literal != null) {
									newChildren[k++] = literal;
								}
							}
							curClause = DeprecatedClause.createClause(map, newChildren);
						} else {
							curClause = DeprecatedClause.createClause(map, children);
						}
					} else {
						curClause = null;
					}
				} else {
					final Literal literal = (Literal) andChild;
					if (literal.var.equals(NodeCreator.varTrue)) {
						if (!literal.positive) {
							throw new RuntimeException("Model is void!");
						}
						curClause = null;
					} else if (literal.var.equals(NodeCreator.varFalse)) {
						if (literal.positive) {
							throw new RuntimeException("Model is void!");
						}
						curClause = null;
					} else {
						curClause = DeprecatedClause.createClause(map, literal);
					}
				}

				addNewClause(curClause);
			}
			workMonitor.worked();

			while (!map.isEmpty()) {
				final String curFeature = map.next().getFeature();
				if (curFeature == null) {
					relevantClauseList.clear();
					relevantClauseSet.clear();
					break;
				}
//				if (map.size() % 10 == 9) {
//					System.out.println(map.size());
//				}
				if (workMonitor.checkCancel()) {
					return null;
				}
				workMonitor.worked();

				// ... create list of clauses that contain this feature
				int relevantIndex = 0;
				final byte[] clauseStates = new byte[relevantClauseList.size()];
				for (int i = 0; i < relevantClauseList.size(); i++) {
					final Clause clause = relevantClauseList.get(i);

					Literal curLiteral = null;
					for (Node clauseChildren : clause.getLiterals()) {
						final Literal literal = (Literal) clauseChildren;
						if (literal.var.equals(curFeature)) {
							if (curLiteral == null) {
								curLiteral = literal;
								clauseStates[relevantIndex] = (byte) (curLiteral.positive ? 1 : 2);
								Collections.swap(relevantClauseList, i, relevantIndex++);
							} else if (literal.positive != curLiteral.positive) {
								clauseStates[relevantIndex - 1] = -1;
								break;
							}
						}
					}
				}

				final CNFSolver solver = new CNFSolver(relevantClauseList.subList(0, relevantIndex));

				// ... combine relevant clauses if possible
				for (int i = relevantIndex - 1; i >= 0; i--) {
					final boolean positive;
					switch (clauseStates[i]) {
					case 1:
						positive = true;
						break;
					case 2:
						positive = false;
						break;
					case -1:
					case 0:
					default:
						continue;
					}

					final Literal[] orChildren = relevantClauseList.get(i).getLiterals();

					if (orChildren.length < 2) {
						continue;
					}

					final Literal[] literalList = new Literal[orChildren.length];
					int removeIndex = orChildren.length;
					int retainIndex = -1;

					for (int j = 0; j < orChildren.length; j++) {
						final Literal literal = orChildren[j].clone();
						if (literal.var.equals(curFeature)) {
							literalList[--removeIndex] = literal;
						} else {
							literal.flip();
							literalList[++retainIndex] = literal;
						}
					}

					// test for generalizability
					if (!solver.isSatisfiable(literalList)) {
						Literal[] retainLiterals = new Literal[retainIndex + 1];
						System.arraycopy(literalList, 0, retainLiterals, 0, retainLiterals.length);
						for (Literal retainedLiteral : retainLiterals) {
							retainedLiteral.flip();
						}

						addNewClause(DeprecatedClause.createClause(map, retainLiterals));

						// try to combine with other clauses
					} else {
						for (int j = i - 1; j >= 0; j--) {
							if ((positive && clauseStates[j] == 2) || (!positive && clauseStates[j] == 1)) {
								final Node[] children2 = relevantClauseList.get(j).getLiterals();
								final Literal[] newChildren = new Literal[orChildren.length + children2.length];

								System.arraycopy(orChildren, 0, newChildren, 0, orChildren.length);
								System.arraycopy(children2, 0, newChildren, orChildren.length, children2.length);

								addNewClause(DeprecatedClause.createClause(map, newChildren, curFeature));
							}
						}
					}
				}
				solver.reset();
				final List<DeprecatedClause> subList = relevantClauseList.subList(0, relevantIndex);
				relevantClauseSet.removeAll(subList);
				for (DeprecatedClause clause : subList) {
					clause.delete(map);
				}
				subList.clear();
				if (map.getGlobalMixedClauseCount() == 0) {
					break;
				}
			}

			// create new clauses list
			final int newClauseSize = newClauseSet.size();
			final Node[] newClauses;
			if (includeBooleanValues) {
				newClauses = new Node[newClauseSize + 3];

				// create clause that contains all retained features
				final Node[] allLiterals = new Node[retainedFeatures.size() + 1];
				int i = 0;
				for (String featureName : retainedFeatures) {
					allLiterals[i++] = new Literal(featureName);
				}
				allLiterals[i] = new Literal(NodeCreator.varTrue);

				newClauses[newClauseSize] = new Or(allLiterals);
				newClauses[newClauseSize + 1] = new Literal(NodeCreator.varTrue);
				newClauses[newClauseSize + 2] = new Literal(NodeCreator.varFalse, false);
			} else {
				newClauses = new Node[newClauseSize];
			}
			int j = 0;
			for (Clause newClause : newClauseSet) {
				newClauses[j++] = new Or(Node.clone(newClause.getLiterals()));
			}

			workMonitor.worked();

			return new And(newClauses);
		} else if (fmNode instanceof Or) {
			for (Node clauseChildren : fmNode.getChildren()) {
				final Literal literal = (Literal) clauseChildren;
				if (features.contains(literal.var)) {
					return includeBooleanValues ? new Literal(NodeCreator.varTrue) : new And();
				}
			}
			return fmNode.clone();
		} else {
			return (features.contains(((Literal) fmNode).var)) ? (includeBooleanValues ? new Literal(NodeCreator.varTrue) : new And()) : fmNode.clone();
		}
	}

	private void addNewClause(final DeprecatedClause curClause) {
		if (curClause != null) {
			if (curClause.getRelevance() == 0) {
				if (!newClauseSet.add(curClause)) {
					curClause.delete(map);
				}
			} else {
				if (relevantClauseSet.add(curClause)) {
					relevantClauseList.add(curClause);
				} else {
					curClause.delete(map);
				}
			}
		}
	}

}
