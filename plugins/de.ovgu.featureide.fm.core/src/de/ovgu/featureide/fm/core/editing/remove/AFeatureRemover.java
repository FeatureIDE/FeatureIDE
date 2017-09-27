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
package de.ovgu.featureide.fm.core.editing.remove;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
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

import de.ovgu.featureide.fm.core.editing.NodeCreator;
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
public abstract class AFeatureRemover implements LongRunningMethod<List<? extends Clause>> {

	/**
	 * For sorting clauses by length. Starting with the longest.
	 */
	private static final class LengthComparator implements Comparator<Clause> {

		@Override
		public int compare(Clause o1, Clause o2) {
			return o2.getLiterals().length - o1.getLiterals().length;
		}
	}

	protected static final Comparator<Clause> lengthComparator = new LengthComparator();

	protected final Node fmNode;

	protected final boolean includeBooleanValues;
	protected final boolean regularCNF;

	protected final List<DeprecatedClause> newRelevantClauseList = new ArrayList<>();
	protected final List<DeprecatedClause> newNewClauseList = new ArrayList<>();
	protected final Set<DeprecatedClause> relevantClauseSet = new HashSet<>();
	protected final Set<DeprecatedClause> newClauseSet = new HashSet<>();
	protected final Set<String> retainedFeatures = new HashSet<>();

	protected List<DeprecatedClause> relevantClauseList;
	protected List<DeprecatedClause> newClauseList;

	protected final Collection<String> features;
	protected Map<Object, Integer> idMap;
	protected String[] featureNameArray;

	protected int[] helper;
	protected DeprecatedFeature[] map;
	protected AFeatureOrderHeuristic heuristic;

	protected int globalMixedClauseCount = 0;

	protected int relevantPosIndex = 0;
	protected int relevantNegIndex = 0;
	protected int newRelevantDelIndex = 0;

	public AFeatureRemover(Node cnf, Collection<String> features) {
		this(cnf, features, true, false);
	}

	public AFeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues) {
		this(cnf, features, includeBooleanValues, false);
	}

	public AFeatureRemover(Node cnf, Collection<String> features, boolean includeBooleanValues, boolean regularCNF) {
		fmNode = cnf;
		this.features = features;
		this.includeBooleanValues = includeBooleanValues;
		this.regularCNF = regularCNF;
	}

	public final Node createNewClauseList(Collection<? extends Clause> clauses) {
		final int newClauseSize = clauses.size();
		final Node[] newClauses;
		if (includeBooleanValues) {
			newClauses = new Node[newClauseSize + 3];

			// create clause that contains all retained features
			final Node[] allLiterals = new Node[retainedFeatures.size() + 1];
			int i = 0;
			for (final String featureName : retainedFeatures) {
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
		for (final Clause newClause : clauses) {
			final int[] newClauseLiterals = newClause.getLiterals();
			final Literal[] literals = new Literal[newClauseLiterals.length];
			int i = literals.length;
			for (int k = 0; k < literals.length; k++) {
				final int child = newClauseLiterals[k];
				literals[--i] = new Literal(featureNameArray[Math.abs(child)], child > 0);
			}
			newClauses[j++] = new Or(literals);
		}
		return new And(newClauses);
	}

	@Override
	public final List<? extends Clause> execute(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
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

	private void addLiteral(Set<String> retainedFeatures, Node orChild) {
		final Literal literal = (Literal) orChild;
		if (literal.var instanceof String) {
			retainedFeatures.add((String) literal.var);
		}
	}

	private void addNewClause(final DeprecatedClause curClause) {
		if (curClause != null) {
			if (curClause.computeRelevance(map)) {
				globalMixedClauseCount++;
			}
			if (curClause.getRelevance() == 0) {
				if (newClauseSet.add(curClause)) {
					newNewClauseList.add(curClause);
				} else {
					deleteClause(curClause);
				}
			} else {
				if (relevantClauseSet.add(curClause)) {
					newRelevantClauseList.add(curClause);
				} else {
					deleteClause(curClause);
				}
			}
		}
	}

	private void collectFeatures() {
		if (fmNode instanceof And) {
			for (final Node andChild : fmNode.getChildren()) {
				if (andChild instanceof Or) {
					for (final Node orChild : andChild.getChildren()) {
						addLiteral(retainedFeatures, orChild);
					}
				} else {
					addLiteral(retainedFeatures, andChild);
				}
			}
		} else if (fmNode instanceof Or) {
			for (final Node orChild : fmNode.getChildren()) {
				addLiteral(retainedFeatures, orChild);
			}
		} else {
			addLiteral(retainedFeatures, fmNode);
		}

		assert (retainedFeatures.containsAll(features));
	}

	private int[] convert(Literal[] newChildren) {
		final int[] literals = new int[newChildren.length];
		for (int j = 0; j < newChildren.length; j++) {
			final Literal child = newChildren[j];
			literals[j] = child.positive ? idMap.get(child.var) : -idMap.get(child.var);
		}
		return literals;
	}

	private void createClauseLists(final Node[] andChildren) {
		for (int i = 0; i < andChildren.length; i++) {
			addNewClause(getClause(andChildren[i]));
		}

		newClauseList = new ArrayList<>(newNewClauseList);
		relevantClauseList = new ArrayList<>(newRelevantClauseList);
		newRelevantClauseList.clear();
		newNewClauseList.clear();

		relevantPosIndex = relevantClauseList.size();
		relevantNegIndex = relevantClauseList.size();
	}

	protected final void deleteClause(final DeprecatedClause curClause) {
		if (curClause.delete(map)) {
			globalMixedClauseCount--;
		}
	}

	protected final void deleteOldRelevantClauses() {
		if (relevantPosIndex < relevantClauseList.size()) {
			final List<DeprecatedClause> subList = relevantClauseList.subList(relevantPosIndex, relevantClauseList.size());
			relevantClauseSet.removeAll(subList);
			for (final DeprecatedClause deprecatedClause : subList) {
				deleteClause(deprecatedClause);
			}
			subList.clear();
		}
	}

	protected final void deleteNewRelevantClauses() {
		if (newRelevantDelIndex < newRelevantClauseList.size()) {
			final List<DeprecatedClause> subList = newRelevantClauseList.subList(newRelevantDelIndex, newRelevantClauseList.size());
			relevantClauseSet.removeAll(subList);
			for (final DeprecatedClause deprecatedClause : subList) {
				deleteClause(deprecatedClause);
			}
		}
	}

	private DeprecatedClause getClause(Node andChild) {
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
					final Literal[] newChildren = new Literal[children.length - absoluteValueCount];
					int k = 0;
					for (int j = 0; j < children.length; j++) {
						final Literal literal = children[j];
						if (literal != null) {
							newChildren[k++] = literal;
						}
					}
					return DeprecatedClause.createClause(convert(newChildren));
				} else {
					return DeprecatedClause.createClause(convert(children));
				}
			} else {
				return null;
			}
		} else {
			final Literal literal = (Literal) andChild;
			if (literal.var.equals(NodeCreator.varTrue)) {
				if (!literal.positive) {
					throw new RuntimeException("Model is void!");
				}
				return null;
			} else if (literal.var.equals(NodeCreator.varFalse)) {
				if (literal.positive) {
					throw new RuntimeException("Model is void!");
				}
				return null;
			} else {
				return DeprecatedClause.createClause(convert(new Literal[] { literal }));
			}
		}
	}

	private List<? extends Clause> handleComplexFormula(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		map = new DeprecatedFeature[idMap.size() + 1];
		for (final String curFeature : features) {
			final Integer id = idMap.get(curFeature);
			map[id] = new DeprecatedFeature(curFeature, id);
		}
		helper = new int[featureNameArray.length];

		// fill sets
		createClauseLists(fmNode.getChildren());

		prepareHeuristics();

		while (heuristic.hasNext()) {
			workMonitor.checkCancel();
			final DeprecatedFeature nextFeature = heuristic.next();
			if (nextFeature == null) {
				break;
			}

			preRedundancyCheck(nextFeature);

			final boolean outputSwitch = (heuristic.size() < 20) || (nextFeature.getClauseCount() > 0);
			if (outputSwitch) {
				final String s = heuristic.size() + ": " + nextFeature.getFeature() + " | #Res: " + nextFeature.getClauseCount() + " | #Rel: "
					+ relevantClauseList.size() + " (-" + nextFeature.getNegativeCount() + ", " + nextFeature.getPositiveCount() + ")";
				System.err.print(s);
			}

			// ... create list of clauses that contain this feature
			sortRelevantList(nextFeature);

			// Remove variable
			resolution(nextFeature);

			if (outputSwitch) {
				final String s = " -> New: " + newNewClauseList.size();
				System.err.print(s);
			}
			final int newCount = newClauseList.size();

			if ((newNewClauseList.size() > 0) || (heuristic.size() == 0)) {
				addNewClauses(nextFeature);
			}

			if (outputSwitch) {
				final String s = "(" + (newClauseList.size() - newCount) + ") -> Rel: " + newRelevantClauseList.size();
				System.err.print(s);
			}

			detectRedundancy(nextFeature);

			if (outputSwitch) {
				final String s = "(" + (newRelevantDelIndex) + ")\n";
				System.err.print(s);
			}

			updateLists();

			if (globalMixedClauseCount == 0) {
				break;
			}
		}

		if (newNewClauseList.size() > 0) {
			newClauseList.addAll(newNewClauseList);
			newNewClauseList.clear();
		}

		release();

		return newClauseList;
	}

	private List<? extends Clause> handleSingleClause(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		for (final Node clauseChildren : fmNode.getChildren()) {
			final Literal literal = (Literal) clauseChildren;
			if (features.contains(literal.var)) {
				return Arrays.asList(new Clause());
			}
		}
		return Arrays.asList(getClause(fmNode));
	}

	private List<? extends Clause> handleSingleLiteral(IMonitor workMonitor) throws TimeoutException, UnkownLiteralException {
		if (features.contains(((Literal) fmNode).var)) {
			return Arrays.asList(new Clause());
		}
		return Arrays.asList(getClause(fmNode));
	}

	private void init() {
		release();

		collectFeatures();

		featureNameArray = new String[retainedFeatures.size() + 1];
		idMap = new HashMap<>(retainedFeatures.size() << 1);

		int id = 1;
		for (final String name : features) {
			idMap.put(name, id);
			featureNameArray[id] = name;
			id++;
		}

		retainedFeatures.removeAll(features);

		for (final String name : retainedFeatures) {
			idMap.put(name, id);
			featureNameArray[id] = name;
			id++;
		}
	}

	private void resolution(DeprecatedFeature nextFeature) {
		final int curFeatureID = nextFeature.getId();
		for (int i = relevantPosIndex; i < relevantNegIndex; i++) {
			final int[] posOrChildren = relevantClauseList.get(i).getLiterals();
			for (int j = relevantNegIndex; j < relevantClauseList.size(); j++) {
				final int[] negOrChildren = relevantClauseList.get(j).getLiterals();
				final int[] newChildren = new int[posOrChildren.length + negOrChildren.length];

				System.arraycopy(posOrChildren, 0, newChildren, 0, posOrChildren.length);
				System.arraycopy(negOrChildren, 0, newChildren, posOrChildren.length, negOrChildren.length);

				addNewClause(DeprecatedClause.createClause(newChildren, curFeatureID, helper));
			}
		}
		newRelevantDelIndex = newRelevantClauseList.size();
	}

	private void sortRelevantList(DeprecatedFeature nextFeature) {
		final int curFeatureID = nextFeature.getId();
		for (int i = 0; i < relevantNegIndex; i++) {
			final Clause clause = relevantClauseList.get(i);
			for (final int literal : clause.getLiterals()) {
				if (literal == -curFeatureID) {
					Collections.swap(relevantClauseList, i--, --relevantNegIndex);
					break;
				}
			}
		}
		relevantPosIndex = relevantNegIndex;
		for (int i = 0; i < relevantPosIndex; i++) {
			final Clause clause = relevantClauseList.get(i);
			for (final int literal : clause.getLiterals()) {
				if (literal == curFeatureID) {
					Collections.swap(relevantClauseList, i--, --relevantPosIndex);
					break;
				}
			}
		}
	}

	private void updateLists() {
		// delete old & redundant relevant
		deleteOldRelevantClauses();

		// delete redundant new
		deleteNewRelevantClauses();

		relevantClauseList.addAll(newRelevantClauseList.subList(0, newRelevantDelIndex));

		newRelevantClauseList.clear();

		relevantPosIndex = relevantClauseList.size();
		relevantNegIndex = relevantClauseList.size();
		newRelevantDelIndex = 0;
	}

	protected void addNewClauses(DeprecatedFeature nextFeature) {
		newClauseList.addAll(newNewClauseList);
		newNewClauseList.clear();
	}

	protected abstract boolean detectRedundancy(DeprecatedFeature next);

	protected final boolean isRemovable(ICNFSolver solver, Clause curClause) {
		final int[] literals = curClause.getLiterals();
		final int[] literals2 = new int[literals.length];
		for (int i = 0; i < literals.length; i++) {
			literals2[i] = -literals[i];
		}
		boolean remove = false;
		try {
			remove = !solver.isSatisfiable(literals2);
		} catch (final TimeoutException e) {
			e.printStackTrace();
		}
		return remove;
	}

	protected abstract void prepareHeuristics();

	protected void preRedundancyCheck(final DeprecatedFeature nextFeature) {}

	protected void release() {
		retainedFeatures.clear();
		newRelevantClauseList.clear();
		newNewClauseList.clear();
		relevantClauseSet.clear();
		newClauseSet.clear();
	}

	protected final void removeNewRelevant(int index) {
		Collections.swap(newRelevantClauseList, index, --newRelevantDelIndex);
	}

	protected final void removeRelevant(int index) {
		Collections.swap(relevantClauseList, index, --relevantPosIndex);
	}

}
