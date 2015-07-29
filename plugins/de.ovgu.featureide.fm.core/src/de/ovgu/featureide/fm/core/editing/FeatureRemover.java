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
package de.ovgu.featureide.fm.core.editing;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.job.LongRunningMethod;
import de.ovgu.featureide.fm.core.job.WorkMonitor;

/**
 * Removes features from a model while retaining dependencies of all other feature.
 * 
 * @author Sebastian Krieter
 */
public class FeatureRemover implements LongRunningMethod<Node> {

	private static class DeprecatedFeature implements Comparable<DeprecatedFeature> {
		private final String feature;

		private int positiveCount;
		private int negativeCount;

		public DeprecatedFeature(String feature) {
			this.feature = feature;
			positiveCount = 0;
			negativeCount = 0;
		}

		public String getFeature() {
			return feature;
		}

		@Override
		public int compareTo(DeprecatedFeature arg0) {
			return (int) Math.signum(arg0.getClauseCount() - getClauseCount());
		}

		public int getClauseCount() {
			return positiveCount * negativeCount;
		}

		public void incPositive() {
			positiveCount++;
		}

		public void incNegative() {
			negativeCount++;
		}

		public void decPositive() {
			positiveCount--;
		}

		public void decNegative() {
			negativeCount--;
		}

		@Override
		public boolean equals(Object arg0) {
			return (arg0 instanceof DeprecatedFeature) && feature.equals(((DeprecatedFeature) arg0).feature);
		}

		@Override
		public int hashCode() {
			return feature.hashCode();
		}

		@Override
		public String toString() {
			return feature + ": " + getClauseCount();
		}
	}

	private static class DeprecatedFeatureMap {

		private final HashMap<String, DeprecatedFeature> map;

		private int globalMixedClauseCount = 0;

		public DeprecatedFeatureMap(Collection<String> features) {
			map = new HashMap<>(features.size() << 1);
			for (String curFeature : features) {
				map.put(curFeature, new DeprecatedFeature(curFeature));
			}
		}

		public DeprecatedFeature next() {
			final Collection<DeprecatedFeature> values = map.values();

			DeprecatedFeature smallestFeature = null;
			if (!values.isEmpty()) {
				final Iterator<DeprecatedFeature> it = values.iterator();
				smallestFeature = it.next();
				while (it.hasNext()) {
					final DeprecatedFeature next = it.next();
					if (next.compareTo(smallestFeature) > 0) {
						smallestFeature = next;
					}
				}
				return map.remove(smallestFeature.getFeature());
			}
			return new DeprecatedFeature(null);
		}

		public boolean isEmpty() {
			return map.isEmpty();
		}

		public DeprecatedFeature get(Object var) {
			return map.get(var);
		}

		public int getGlobalMixedClauseCount() {
			return globalMixedClauseCount;
		}

		public void incGlobalMixedClauseCount() {
			globalMixedClauseCount++;
		}

		public void decGlobalMixedClauseCount() {
			globalMixedClauseCount--;
		}
	}

	private static class Clause {

		private static final class LiteralComparator implements Comparator<Literal> {
			@Override
			public int compare(Literal arg0, Literal arg1) {
				if (arg0.positive == arg1.positive) {
					return ((String) arg0.var).compareTo((String) arg1.var);
				} else if (arg0.positive) {
					return -1;
				} else {
					return 1;
				}
			}
		}

		private static final LiteralComparator literalComparator = new LiteralComparator();

		private Literal[] literals;
		private int relevance;

		public static Clause createClause(DeprecatedFeatureMap map, Literal[] newLiterals, String curFeature) {
			final HashSet<Literal> literalSet = new HashSet<>(newLiterals.length << 1);
			for (Literal literal : newLiterals) {
				if (!curFeature.equals(literal.var)) {
					final Literal negativeliteral = literal.clone();
					negativeliteral.flip();

					if (literalSet.contains(negativeliteral)) {
						return null;
					} else {
						literalSet.add(literal);
					}
				}
			}

			final Clause clause = new Clause(literalSet.toArray(new Literal[0]));
			clause.computeRelevance(map);
			return clause;
		}

		public static Clause createClause(DeprecatedFeatureMap map, Literal[] newLiterals) {
			final HashSet<Literal> literalSet = new HashSet<>(newLiterals.length << 1);
			for (Literal literal : newLiterals) {
				final Literal negativeliteral = literal.clone();
				negativeliteral.flip();

				if (literalSet.contains(negativeliteral)) {
					return null;
				} else {
					literalSet.add(literal);
				}
			}

			final Clause clause = new Clause(literalSet.toArray(new Literal[0]));
			clause.computeRelevance(map);
			return clause;
		}

		public static Clause createClause(DeprecatedFeatureMap map, Literal newLiteral) {
			final Clause clause = new Clause(new Literal[] { newLiteral });
			final DeprecatedFeature df = map.get(newLiteral.var);
			if (df != null) {
				clause.relevance++;
			}
			return clause;
		}

		private Clause(Literal[] literals) {
			this.literals = literals;
			Arrays.sort(this.literals, literalComparator);
			this.relevance = 0;
		}

		public Literal[] getLiterals() {
			return literals;
		}

		private void computeRelevance(DeprecatedFeatureMap map) {
			for (Literal literal : literals) {
				final DeprecatedFeature df = map.get(literal.var);
				if (df != null) {
					relevance++;
					if (literal.positive) {
						df.incPositive();
					} else {
						df.incNegative();
					}
				}
			}
			if (relevance > 0 && relevance < literals.length) {
				map.incGlobalMixedClauseCount();
			}
		}

		public void delete(DeprecatedFeatureMap map) {
			if (literals != null && literals.length > 1) {
				for (Literal literal : literals) {
					final DeprecatedFeature df = map.get(literal.var);
					if (df != null) {
						if (literal.positive) {
							df.decPositive();
						} else {
							df.decNegative();
						}
					}
				}
				if (relevance > 0 && relevance < literals.length) {
					map.decGlobalMixedClauseCount();
				}
				literals = null;
			}
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(literals);
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null || getClass() != obj.getClass())
				return false;
			return Arrays.equals(literals, ((Clause) obj).literals);
		}

		@Override
		public String toString() {
			return "Clause [literals=" + Arrays.toString(literals) + "]";
		}

		public int getRelevance() {
			return relevance;
		}

	}

	private static class CNFSolver {

		private final HashMap<Object, Integer> varToInt;
		private final ISolver solver;

		public CNFSolver(Collection<Clause> clauses) {
			varToInt = new HashMap<Object, Integer>();
			for (Clause clause : clauses) {
				for (Literal literal : clause.getLiterals()) {
					final Object var = literal.var;
					if (!varToInt.containsKey(var)) {
						int index = varToInt.size() + 1;
						varToInt.put(var, index);
					}
				}
			}

			solver = SolverFactory.newDefault();
			solver.setTimeoutMs(1000);
			solver.newVar(varToInt.size());

			try {
				for (Clause node : clauses) {
					final Literal[] literals = node.getLiterals();
					int[] clause = new int[literals.length];
					int i = 0;
					for (Literal child : literals) {
						clause[i++] = getIntOfLiteral(child);
					}
					solver.addClause(new VecInt(clause));
				}
			} catch (ContradictionException e) {
				throw new RuntimeException(e);
			}
		}

		private int getIntOfLiteral(Literal node) {
			final int value = varToInt.get(node.var);
			return node.positive ? value : -value;
		}

		public boolean isSatisfiable(Literal[] literals) throws TimeoutException {
			final int[] unitClauses = new int[literals.length];
			int i = 0;
			for (Literal literal : literals) {
				unitClauses[i++] = getIntOfLiteral(literal);
			}
			return solver.isSatisfiable(new VecInt(unitClauses));
		}

		public void reset() {
			solver.reset();
		}

	}

	private final FeatureModel fm;

	private final Collection<String> features;

	// all clauses that have both kinds of literals (remove AND retain)
	private List<Clause> relevantClauseList;
	private Set<Clause> relevantClauseSet;

	// list for all new construct clauses
	private Set<Clause> newClauseSet;

	private DeprecatedFeatureMap map;

	public FeatureRemover(FeatureModel fm, Collection<String> features) {
		this.fm = fm;
		this.features = features;
	}

	public Node execute(WorkMonitor workMonitor) throws TimeoutException {
		workMonitor.setMaxAbsoluteWork(features.size() + 3);
		Node fmNode = NodeCreator.createNodes(fm).toCNF();
		workMonitor.worked();
		if (fmNode instanceof And) {
			final Node[] andChildren = fmNode.getChildren();

			relevantClauseList = new ArrayList<>(andChildren.length);
			relevantClauseSet = new HashSet<>(relevantClauseList);

			newClauseSet = new HashSet<>(andChildren.length);

			map = new DeprecatedFeatureMap(features);

			// fill first two lists
			for (int i = 0; i < andChildren.length; i++) {
				Node andChild = andChildren[i];

				final Clause curClause;

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
							curClause = Clause.createClause(map, newChildren);
						} else {
							curClause = Clause.createClause(map, children);
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
						curClause = Clause.createClause(map, literal);
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
				//	System.out.println(map.size());
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

						addNewClause(Clause.createClause(map, retainLiterals));

						// try to combine with other clauses
					} else {
						for (int j = i - 1; j >= 0; j--) {
							if ((positive && clauseStates[j] == 2) || (!positive && clauseStates[j] == 1)) {
								final Node[] children2 = relevantClauseList.get(j).getLiterals();
								final Literal[] newChildren = new Literal[orChildren.length + children2.length];

								System.arraycopy(orChildren, 0, newChildren, 0, orChildren.length);
								System.arraycopy(children2, 0, newChildren, orChildren.length, children2.length);

								addNewClause(Clause.createClause(map, newChildren, curFeature));
							}
						}
					}
				}
				solver.reset();
				final List<Clause> subList = relevantClauseList.subList(0, relevantIndex);
				relevantClauseSet.removeAll(subList);
				for (Clause clause : subList) {
					clause.delete(map);
				}
				subList.clear();
				if (map.getGlobalMixedClauseCount() == 0) {
					break;
				}
			}

			// create clause that contains all retained features
			final Node[] allLiterals = new Node[fm.getNumberOfFeatures() - features.size() + 1];
			int i = 0;
			for (String featureName : fm.getFeatureNames()) {
				if (!features.contains(featureName)) {
					allLiterals[i++] = new Literal(featureName);
				}
			}
			allLiterals[i] = new Literal(NodeCreator.varTrue);

			// create new clauses list
			final int newClauseSize = newClauseSet.size();
			final Node[] newClauses = new Node[newClauseSize + 3];

			int j = 0;
			for (Clause newClause : newClauseSet) {
				newClauses[j++] = new Or(newClause.getLiterals());
			}

			newClauses[newClauseSize] = new Or(allLiterals);
			newClauses[newClauseSize + 1] = new Literal(NodeCreator.varTrue);
			newClauses[newClauseSize + 2] = new Literal(NodeCreator.varFalse, false);

			fmNode.setChildren(newClauses);
			
			workMonitor.worked();

			return fmNode;
		} else if (fmNode instanceof Or) {
			for (Node clauseChildren : fmNode.getChildren()) {
				final Literal literal = (Literal) clauseChildren;
				if (features.contains(literal.var)) {
					return new Literal(NodeCreator.varTrue);
				}
			}
			workMonitor.worked();
			return fmNode;
		} else {
			workMonitor.worked();
			return (features.contains(((Literal) fmNode).var)) ? new Literal(NodeCreator.varTrue) : fmNode;
		}
	}

	private void addNewClause(final Clause curClause) {
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
