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
package de.ovgu.featureide.fm.core.editing.remove;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.CNFSolver2;
import de.ovgu.featureide.fm.core.editing.cnf.Clause;
import de.ovgu.featureide.fm.core.editing.cnf.ICNFSolver;
import de.ovgu.featureide.fm.core.editing.cnf.UnkownLiteralException;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.monitor.IMonitor;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 * 
 * @author Sebastian Krieter
 */
public class FeatureRemover implements LongRunningMethod<Node> {

	public static final int RR_NONE = 0;
	public static final int RR_SIMPLE = 1;
	public static final int RR_COMPLEX = 2;
	
	public static final int FO_PREORDER = 0;
	public static final int FO_MINCLAUSE = 1;
	public static final int FO_POSTORDER = 2;
	public static final int FO_REV_LEVELORDER = 4;
	
	public static int PARAM_REDUNDANCY_REMOVAL = 3;
	public static int PARAM_FEATURE_ORDER = 1;
	public static IFeatureModel featureModel = null;

	private final Node fmNode;

	private final Collection<String> features;

	private final boolean includeBooleanValues;
	private final boolean regularCNF;

	private final List<DeprecatedClause> newRelevantClauseList = new ArrayList<>();

	private List<DeprecatedClause> relevantClauseList;
	private Set<DeprecatedClause> relevantClauseSet;
	private Set<DeprecatedClause> newClauseSet;
	private List<DeprecatedClause> orgClauseList;
	private Set<String> retainedFeatures;
	private Map<Object, Integer> idMap;

	private String[] featureNameArray;
	private boolean[] removedFeatures;

	private ICNFSolver solver;

	private DeprecatedFeature[] map;
	private AFeatureOrderHeuristic heuristic;

	private int globalMixedClauseCount = 0;

	int relevantPosIndex = 0;
	int relevantNegIndex = 0;

	public FeatureRemover(Node cnf, Collection<String> features) {
		this(cnf, features, true, false);
	}

	public FeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues) {
		this(cnf, features, includeBooleanValues, false);
	}

	public FeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues, boolean regularCNF) {
		this.fmNode = cnf;
		this.features = features;
		this.includeBooleanValues = includeBooleanValues;
		this.regularCNF = regularCNF;
	}

	private void addLiteral(Set<String> retainedFeatures, Node orChild) {
		final Literal literal = (Literal) orChild;
		if (literal.var instanceof String) {
			retainedFeatures.add((String) literal.var);
		}
	}

	private void collectFeatures() {
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

		assert (retainedFeatures.containsAll(features));
	}

	private void init() {
		retainedFeatures = new HashSet<>();

		collectFeatures();

		removedFeatures = new boolean[retainedFeatures.size() + 1];

		featureNameArray = new String[retainedFeatures.size() + 1];
		idMap = new HashMap<>(retainedFeatures.size() << 1);

		int id = 1;
		for (String name : features) {
			idMap.put(name, id);
			featureNameArray[id] = name;
			id++;
		}

		retainedFeatures.removeAll(features);

		for (String name : retainedFeatures) {
			idMap.put(name, id);
			featureNameArray[id] = name;
			id++;
		}
	}

	public Node execute(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		// Collect all features in the prop node and remove TRUE and FALSE
		init();

		// CNF with more than one clause
		if (fmNode instanceof And) {
			return handleComplexFormula(workMonitor);
		} else if (fmNode instanceof Or) {
			return handleSingleClause(workMonitor);
		} else {
			return handleSingleLiteral(workMonitor);
		}
	}

	public Node handleSingleClause(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		for (Node clauseChildren : fmNode.getChildren()) {
			final Literal literal = (Literal) clauseChildren;
			if (features.contains(literal.var)) {
				return includeBooleanValues ? (regularCNF ? new Or(new Literal(NodeCreator.varTrue, true)) : new Literal(NodeCreator.varTrue, true))
						: new And();
			}
		}
		return fmNode.clone();
	}

	public Node handleSingleLiteral(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		return (features.contains(((Literal) fmNode).var)) ? (includeBooleanValues ? new Literal(NodeCreator.varTrue) : new And()) : fmNode.clone();
	}

	public Node handleComplexFormula(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		final Node[] andChildren = fmNode.getChildren();

		relevantClauseList = new ArrayList<>(andChildren.length);
		relevantClauseSet = new HashSet<>(andChildren.length << 1);
		newClauseSet = new HashSet<>(andChildren.length << 1);
		map = new DeprecatedFeature[idMap.size() + 1];
		for (String curFeature : features) {
			map[idMap.get(curFeature)] = new DeprecatedFeature(curFeature);
		}
		switch (PARAM_FEATURE_ORDER) {
		case FO_PREORDER:
			heuristic = new PreorderHeuristic(map, features.size(), featureModel);
			break;
		case FO_POSTORDER:
			heuristic = new PostorderHeuristic(map, features.size(), featureModel);
			break;
		case FO_REV_LEVELORDER:
			heuristic = new ReverseLevelOrderHeuristic(map, features.size(), featureModel);
			break;
		case FO_MINCLAUSE:
			heuristic = new MinimumClauseHeuristic(map, features.size());
			break;
		default:
			return null;
		}

		// fill sets
		createClauseList(andChildren);
		relevantClauseList.addAll(newRelevantClauseList);
		newRelevantClauseList.clear();

		createSolver();

		workMonitor.setRemainingWork(heuristic.size() + 1);

		final double localFactor = 1.2;
		final double globalFactor = 1.5;

		final int maxClauseCountLimit = (int) Math.floor(globalFactor * relevantClauseList.size());

		relevantPosIndex = 0;
		relevantNegIndex = relevantClauseList.size();

		while (heuristic.hasNext()) {
			workMonitor.checkCancel();
			final DeprecatedFeature next = heuristic.next();
			final String curFeature = next.getFeature();
			final int curFeatureID = idMap.get(curFeature);

			if (PARAM_REDUNDANCY_REMOVAL > 0) {
				final long estimatedClauseCount = next.getClauseCount();
				final int curClauseCountLimit = (int) Math.floor(localFactor * ((relevantNegIndex - relevantPosIndex) + newRelevantClauseList.size()));

				if ((estimatedClauseCount > maxClauseCountLimit) || (estimatedClauseCount > curClauseCountLimit)) {
					if ((PARAM_REDUNDANCY_REMOVAL & RR_SIMPLE) != 0) {
						detectRedundantConstraintsSimple();
					}
					if ((PARAM_REDUNDANCY_REMOVAL & RR_COMPLEX) != 0) {
						detectRedundantConstraintsComplex();
					}
				}
			}

			removeOldClauses();

			// ... create list of clauses that contain this feature
			sortRelevantList(curFeatureID);

			// Remove variable
			resolution(curFeatureID);

			removedFeatures[curFeatureID] = true;

			if (globalMixedClauseCount == 0) {
				break;
			}
		}

		release();

		// create new clauses list
		final Node[] newClauses = createNewClauseList();
		workMonitor.step();

		return new And(newClauses);
	}

	private void release() {
		relevantClauseList.clear();
		relevantClauseSet.clear();
		solver.reset();

		solver = null;
		relevantClauseList = null;
		relevantClauseSet = null;
		removedFeatures = null;
	}

	private void detectRedundantConstraintsComplex() {
		createOrgSolver();
		for (int i = relevantPosIndex; i < relevantNegIndex; i++) {
			final DeprecatedClause mainClause = relevantClauseList.get(i);
			if (remove(mainClause)) {
				Collections.swap(relevantClauseList, i, --relevantNegIndex);
				i--;
			} else {
				solver.addClause(mainClause);
			}
		}

		int tempIndex = 0;
		int i = 0;
		for (DeprecatedClause mainClause : newRelevantClauseList) {
			if (remove(mainClause)) {
				Collections.swap(newRelevantClauseList, i, tempIndex++);
			} else {
				solver.addClause(mainClause);
			}
			i++;
		}
		final List<DeprecatedClause> subList = newRelevantClauseList.subList(0, tempIndex);
		for (DeprecatedClause deprecatedClause : subList) {
			if (deprecatedClause.delete(map)) {
				globalMixedClauseCount--;
			}
		}
		subList.clear();
	}

	private void detectRedundantConstraintsSimple() {
		for (int i = relevantPosIndex; i < relevantNegIndex; i++) {
			final DeprecatedClause mainClause = relevantClauseList.get(i);
			for (int j = i + 1; j < relevantNegIndex; j++) {
				final DeprecatedClause subClause = relevantClauseList.get(j);
				final Clause contained = Clause.contained(mainClause, subClause);
				if (contained != null) {
					if (subClause == contained) {
						Collections.swap(relevantClauseList, j, --relevantNegIndex);
						j--;
					} else {
						Collections.swap(relevantClauseList, i, --relevantNegIndex);
						i--;
						break;
					}
				}
			}
		}

		int tempIndex = newRelevantClauseList.size();
		if (tempIndex > 0) {
			for (int i = 0; i < tempIndex; i++) {
				final DeprecatedClause mainClause = newRelevantClauseList.get(i);
				for (int j = i + 1; j < tempIndex; j++) {
					final DeprecatedClause subClause = newRelevantClauseList.get(j);
					final Clause contained = Clause.contained(mainClause, subClause);
					if (contained != null) {
						if (subClause == contained) {
							Collections.swap(newRelevantClauseList, j, --tempIndex);
							j--;
						} else {
							Collections.swap(newRelevantClauseList, i, --tempIndex);
							i--;
							break;
						}
					}
				}
			}

			for (int i = relevantPosIndex; i < relevantNegIndex; i++) {
				final DeprecatedClause mainClause = relevantClauseList.get(i);
				for (int j = 0; j < tempIndex; j++) {
					final DeprecatedClause subClause = newRelevantClauseList.get(j);
					final Clause contained = Clause.contained(mainClause, subClause);
					if (contained != null) {
						if (subClause == contained) {
							Collections.swap(newRelevantClauseList, j, --tempIndex);
							j--;
						} else {
							Collections.swap(relevantClauseList, i, --relevantNegIndex);
							i--;
							break;
						}
					}
				}
			}

			if (tempIndex < newRelevantClauseList.size()) {
				final List<DeprecatedClause> subList = newRelevantClauseList.subList(tempIndex, newRelevantClauseList.size());
				for (DeprecatedClause deprecatedClause : subList) {
					deprecatedClause.delete(map);
				}
				subList.clear();
			}
		}
	}

	private void removeOldClauses() {
		for (int i = 0; i < relevantPosIndex; i++) {
			relevantClauseList.get(i).delete(map);
		}
		for (int i = relevantNegIndex; i < relevantClauseList.size(); i++) {
			relevantClauseList.get(i).delete(map);
		}
		relevantClauseSet.removeAll(relevantClauseList.subList(0, relevantPosIndex));
		if (relevantNegIndex < relevantClauseList.size()) {
			relevantClauseSet.removeAll(relevantClauseList.subList(relevantNegIndex, relevantClauseList.size()));
		}
		final List<DeprecatedClause> subList = relevantClauseList.subList(relevantPosIndex, relevantNegIndex);
		final ArrayList<DeprecatedClause> tempRelevantClauseList = new ArrayList<>(subList.size() + newRelevantClauseList.size());
		tempRelevantClauseList.addAll(subList);
		tempRelevantClauseList.addAll(newRelevantClauseList);
		newRelevantClauseList.clear();
		relevantClauseList.clear();

		relevantClauseList = tempRelevantClauseList;
	}

	private void sortRelevantList(int curFeatureID) {
		relevantPosIndex = 0;
		relevantNegIndex = relevantClauseList.size();
		for (int i = 0; i < relevantNegIndex; i++) {
			final Clause clause = relevantClauseList.get(i);
			for (int literal : clause.getLiterals()) {
				if (Math.abs(literal) == curFeatureID) {
					if (literal > 0) {
						Collections.swap(relevantClauseList, i, relevantPosIndex);
						relevantPosIndex++;
					} else {
						relevantNegIndex--;
						Collections.swap(relevantClauseList, i, relevantNegIndex);
						i--;
					}
					break;
				}
			}
		}
	}

	private void resolution(final int curFeatureID) {
		for (int i = 0; i < relevantPosIndex; i++) {
			final int[] orChildren = relevantClauseList.get(i).getLiterals();
			for (int j = relevantNegIndex; j < relevantClauseList.size(); j++) {
				final int[] children2 = relevantClauseList.get(j).getLiterals();
				final int[] newChildren = new int[orChildren.length + children2.length];

				System.arraycopy(orChildren, 0, newChildren, 0, orChildren.length);
				System.arraycopy(children2, 0, newChildren, orChildren.length, children2.length);

				addNewClause(DeprecatedClause.createClause(newChildren, curFeatureID));
			}
		}
	}

	private void createClauseList(final Node[] andChildren) {
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
						curClause = DeprecatedClause.createClause(convert(newChildren));
					} else {
						curClause = DeprecatedClause.createClause(convert(children));
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
					curClause = DeprecatedClause.createClause(convert(new Literal[] { literal }));
				}
			}

			addNewClause(curClause);
		}
		//		orgClauseList = new ArrayList<>(newClauseSet);
	}

	@SuppressWarnings("unused")
	private void removeRedundantConstraintsComplex() {
		if (solver != null) {
			solver.reset();
		}
		solver = new CNFSolver(orgClauseList, retainedFeatures.size());
		newClauseSet.removeAll(orgClauseList);

		for (DeprecatedClause mainClause : newClauseSet) {
			if (!remove(mainClause)) {
				solver.addClause(mainClause);
				orgClauseList.add(mainClause);
			}
		}
	}

	private Node[] createNewClauseList() {
		//		removeRedundantConstraintsComplex();
		//		Collection<DeprecatedClause> clauses = orgClauseList;
		final Collection<DeprecatedClause> clauses = newClauseSet;

		final int newClauseSize = clauses.size();
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
			if (regularCNF) {
				newClauses[newClauseSize + 1] = new Or(new Literal(NodeCreator.varTrue, true));
				newClauses[newClauseSize + 2] = new Or(new Literal(NodeCreator.varFalse, false));
			} else {
				newClauses[newClauseSize + 1] = new Literal(NodeCreator.varTrue, true);
				newClauses[newClauseSize + 2] = new Literal(NodeCreator.varFalse, false);
			}
		} else {
			newClauses = new Node[newClauseSize];
		}
		int j = 0;
		for (Clause newClause : clauses) {
			final int[] newClauseLiterals = newClause.getLiterals();
			final Literal[] literals = new Literal[newClauseLiterals.length];
			int i = literals.length;
			for (int k = 0; k < literals.length; k++) {
				final int child = newClauseLiterals[k];
				literals[--i] = new Literal(featureNameArray[Math.abs(child)], child > 0);
			}
			newClauses[j++] = new Or(literals);
		}
		return newClauses;
	}

	private void createSolver() {
		if (solver != null) {
			solver.reset();
		}
		final List<Clause> clauseList = new ArrayList<>(relevantClauseList.size() + newClauseSet.size());
		clauseList.addAll(relevantClauseList);
		clauseList.addAll(newClauseSet);
		solver = new CNFSolver(clauseList, idMap.size());
	}

	private void createOrgSolver() {
		if (solver != null) {
			solver.reset();
		}
		solver = new CNFSolver2(newClauseSet, removedFeatures);
	}

	private int[] convert(Literal[] newChildren) {
		final int[] literals = new int[newChildren.length];
		for (int j = 0; j < newChildren.length; j++) {
			final Literal child = newChildren[j];
			literals[j] = child.positive ? idMap.get(child.var) : -idMap.get(child.var);
		}
		return literals;
	}

	private void addNewClause(final DeprecatedClause curClause) {
		if (curClause != null) {
			if (curClause.computeRelevance(map)) {
				globalMixedClauseCount++;
			}
			if (curClause.getRelevance() == 0) {
				if (!newClauseSet.add(curClause)) {
					curClause.delete(map);
				}
			} else {
				if (relevantClauseSet.add(curClause)) {
					newRelevantClauseList.add(curClause);
				} else {
					curClause.delete(map);
				}
			}
		}
	}

	private boolean remove(DeprecatedClause curClause) {
		final int[] literals = curClause.getLiterals();
		final int[] literals2 = new int[literals.length];
		for (int i = 0; i < literals.length; i++) {
			literals2[i] = -literals[i];
		}
		boolean remove = false;
		try {
			remove = !solver.isSatisfiable(literals2);
		} catch (TimeoutException e) {
			e.printStackTrace();
		}
		return remove;
	}

}
