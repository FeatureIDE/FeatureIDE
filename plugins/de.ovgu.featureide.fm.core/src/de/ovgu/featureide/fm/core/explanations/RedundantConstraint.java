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
package de.ovgu.featureide.fm.core.explanations;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * Generates explanations for redundant constraints using {@link LTMS}.
 * 
 * @author Sofia Ananieva
 * @author Timo Guenther
 */
public class RedundantConstraint {
	/**
	 * Returns an explanation why the given constraint of the given feature model is redundant.
	 * Sets several initial truth value assumptions that lead to a violation of the redundant constraint.
	 * Then propagates the values until a violation in a clause occurs.
	 * Finally combines all generated explanations into one.
	 * @param fm the feature model without the redundant constraint
	 * @param defectConstraint the redundant constraint
	 * @return an explanation why the given constraint of the given feature model is redundant
	 */
	public Explanation explain(IFeatureModel fm, IConstraint defectConstraint) {
		final Explanation explanation = new Explanation();
		explanation.setExplanationCount(0);
		Node cnf = NodeCreator.createNodes(fm, true).toCNF();
		cnf = eliminateTrueClauses(cnf);
		final LTMS ltms = new LTMS(cnf);
		for (final Map<Object, Boolean> assignment : getContradictingAssignments(defectConstraint.getNode())) {
			ltms.setPremises(assignment);
			explanation.addExplanation(ltms.getExplanation());
		}
		explanation.setDefectRedundantConstraint(defectConstraint);
		explanation.setFeatureModel(fm);
		return explanation;
	}
	
	/**
	 * Returns all value assumptions for which the conjunctive normal form of a redundant constraint is false.
	 * @param clause any clause (not necessarily in conjunctive normal form)
	 * @return A list which contains a mapping between a variable and its truth value
	 */
	private static Set<Map<Object, Boolean>> getContradictingAssignments(Node clause) {
		final Set<Map<Object, Boolean>> assignments = getAssignments(clause);
		for (final Iterator<Map<Object, Boolean>> it = assignments.iterator(); it.hasNext();) {
			final Map<Object, Boolean> assignment = it.next();
			if (clause.getValue(assignment)) { //not a contradiction
				it.remove();
			}
		}
		return assignments;
	}
	
	/**
	 * Returns all possible truth value assignments for the given clause.
	 * @param clause any clause (not necessarily in conjunctive normal form)
	 * @return all possible truth value assignments for the given clause
	 */
	private static Set<Map<Object, Boolean>> getAssignments(Node clause) {
		final Set<Object> keys = new LinkedHashSet<>();
		for (final Literal literal : clause.getLiterals()) {
			keys.add(literal.var);
		}
		final Set<Map<Object, Boolean>> assignments = new LinkedHashSet<>();
		for (int assignment = 0; assignment < 1 << keys.size(); assignment++) { //2^n possible assignments
			final Map<Object, Boolean> map = new LinkedHashMap<Object, Boolean>();
			int i = 0;
			for (final Object key : keys) {
				map.put(key, (assignment & (1 << i)) != 0);
				i++;
			}
			assignments.add(map);
		}
		return assignments;
	}
	
	/**
	 * Removes clauses which are added in Node Creator while eliminateAbstractVariables().
	 * Such clauses are of the form True & -False & (A|B|C|True) and can be removed because
	 * they are true and don't change the semantic of a formula.
	 * @param node the node to remove true clauses from
	 * @return a node without true clauses
	 */
	private static Node eliminateTrueClauses(Node node) {
		LinkedList<Node> updatedNodes = new LinkedList<Node>();
		for (Node child : node.getChildren())
			if (!child.toString().contains("True") && !child.toString().contains("False"))
				updatedNodes.add(child);
		return updatedNodes.isEmpty() ? null : new And(updatedNodes);
	}
}
