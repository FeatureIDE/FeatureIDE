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

import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.LinkedHashSet;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.Bookkeeping;
import de.ovgu.featureide.fm.core.explanations.LTMS;

import org.prop4j.Literal;
import org.prop4j.Node;

/**
 * The class Redundancy generates explanations for redundant constraints. It uses a logic truth maintenance system (LTMS)
 * and boolean constraint propagation (BCP) which functions as an inference engine of the LTMS.
 * 
 * @author "Ananieva Sofia"
 */
public class Redundancy {

	/**
	 * A hash map for storing truth values, reasons and antecedents per literal.
	 * Key = literal.var, value = class Bookkeeping
	 */
	private HashMap<Object, Bookkeeping> valueMap = new HashMap<Object, Bookkeeping>();
	/**
	 * The model before changes (usually without redundant constraints).
	 */
	private IFeatureModel model;
	/**
	 * The model after changes (with redundant constraint).
	 */
	private static IFeatureModel newModel;
	/**
	 * The list which contains a literal of a respective feature from the redundant constraint.
	 */
	private ArrayList<Literal> featRedundantConstr = null;

	/**
	 * A hash map for storing the number of occurrences of explanation parts.
	 */
	private static HashMap<String, Integer> weightedExplRedundancy = new HashMap<String, Integer>();

	/**
	 * Count explanations for one redundant constraint.
	 */
	private static int cntExpl = 1;

	/**
	 * Checks whether a string contains a delimiter and removes the delimiter.
	 * 
	 * @param list the list with all strings
	 * @param str String to check its occurrence in the list
	 * @param del delimiter
	 * @return true, if the string contains a delimiter, else false
	 */
	static boolean containsIgnoreSuffix(List<String> list, String str, String del) {
		for (String s : list) {
			int index1 = s.lastIndexOf(del);
			if (index1 >= 0)
				s = s.substring(0, index1);
			int index2 = str.lastIndexOf(del);
			if (index2 >= 0)
				str = str.substring(0, index2);
			if (s.equals(str)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Explains why a constraint is redundant. Assumes values for features of the redundant constraint
	 * which lead to a false formula of the redundant constraint and propagates this values until a violation
	 * in a clause occurs.
	 * 
	 * @param oldModel The feature model without the redundant constraint
	 * @param redundantConstraint The redundant constraint
	 */
	public List<String> explain(IFeatureModel oldModel, IFeatureModel newModel, IConstraint redundantConstraint) {
		model = oldModel; // the model without the redundant constraint
		setNewModel(newModel);
		featRedundantConstr = getLiterals(redundantConstraint.getNode());
		featRedundantConstr = new ArrayList<Literal>(new LinkedHashSet<Literal>(featRedundantConstr)); // remove duplicates from list
		weightedExplRedundancy.clear();
		cntExpl = 0;

		List<String> explList = new ArrayList<>();
		explList.add("\nConstraint is redundant, because:");
		Node node = NodeCreator.createNodes(oldModel, true).toCNF();
		Node redundantConstr = redundantConstraint.getNode().toCNF();

		//remember all truth values which lead to an invalid CNF
		ArrayList<HashMap<Object, Integer>> values = getFeatureValues(featRedundantConstr.size(), redundantConstr, featRedundantConstr);
		Node[] clauses = node.getChildren();

		List<String> reasons = new ArrayList<String>(); // collect all explanations into array without duplicates

		for (HashMap<Object, Integer> map : values) {
			setTruthValueToUnknown(clauses); //(re)set all literal values to -1

			for (Literal l : featRedundantConstr) {
				valueMap.get(l.var).value = map.get(l.var);// get literal from origin map and set its value according to invalid CNF
				valueMap.get(l.var).premise = true;
			}
			LTMS ltms = new LTMS(model, valueMap, featRedundantConstr);
			List<String> tmpExplList = ltms.explainRedundantConstraint(clauses, map);

			for (String s : tmpExplList) {
				if (!containsIgnoreSuffix(reasons, s, "$")) {
					reasons.add(s);
				}
			}
		}
		if (reasons.isEmpty()) {
			explList.add("No explanation possible");
		} else {
			for (String s : reasons) {
				explList.add(s);
			}
		}
		LTMS.weightExpl(explList, weightedExplRedundancy, cntExpl);
		return explList;
	}

	/**
	 * Sets the model with the new redundant constraint.
	 * 
	 * @param Feature model The model with the new constraint
	 */
	public static void setNewModel(IFeatureModel model) {
		newModel = model;
	}

	/**
	 * Gets the model with the new constraint. Used for tool tips to get the correct constraint index.
	 * 
	 * @return newModel The model with the new constraint
	 */
	public static IFeatureModel getNewModel() {
		return newModel;
	}

	/**
	 * Gets map which contains all explanation parts and their occurrence in all explanations.
	 * 
	 * @return weightedExplRedundancy The map with weighted explanation parts
	 */
	public static HashMap<String, Integer> getWeighted() {
		return weightedExplRedundancy;
	}

	/**
	 * Gets the number of all explanations for one redundant constraint.
	 * 
	 * @return cntExpl The number of all explanations
	 */
	public static int getCntExpl() {
		return cntExpl;
	}

	/**
	 * Increments the number of all explanations for one redundant constraint.
	 * 
	 * @return cntExpl An incremented count of explanations
	 */
	public static int setCntExpl() {
		return cntExpl++;
	}

	/**
	 * Returns a list which contains literals of a given node.
	 * 
	 * @param node the node which contains the literals
	 * @return res An array list which contains literals of a given node
	 */
	private ArrayList<Literal> getLiterals(Node node) {
		ArrayList<Literal> res = new ArrayList<Literal>();
		if (node instanceof Literal) {
			res.add((Literal) node);
			return res;
		}
		Node[] childs = node.getChildren();
		if (childs != null) {
			for (Node child : childs) {
				res.addAll(getLiterals(child));
			}
		}
		return res;
	}

	/**
	 * Sets the truth value of every literal in the conjunctive normal form to -1 (unknown)
	 * 
	 * @param clausesFromCNF clauses of the conjunctive normal form
	 */
	private void setTruthValueToUnknown(Node[] clausesFromCNF) {
		for (int j = 0; j < clausesFromCNF.length; j++) { // for all clauses of the cnf 
			Node clause = clausesFromCNF[j];
			Node[] features = clause.getChildren();
			if (features == null) {
				final Literal literal = (Literal) clause;
				Bookkeeping expl = new Bookkeeping(literal.var, -1, null, null, false);
				valueMap.put(literal.var, expl);
				continue;
			}
			for (Node feature : features) {
				final Literal literal = (Literal) feature;
				Bookkeeping expl = new Bookkeeping(literal.var, -1, null, null, false);
				valueMap.put(literal.var, expl);
			}
		}
	}

	/**
	 * Returns all value assumptions for which the conjunctive normal form of a redundant constraint is false.
	 * 
	 * @param n the number of variables
	 * @param cnf the clauses of the redundant constraint in conjunctive normal form
	 * @param literals the literals from the redundant constraint
	 * @return res A list which contains a mapping between a variable and its truth value
	 */
	private ArrayList<HashMap<Object, Integer>> getFeatureValues(int n, Node cnf, ArrayList<Literal> literals) {
		HashMap<Object, Integer> map = new HashMap<Object, Integer>();
		ArrayList<HashMap<Object, Integer>> res = new ArrayList<HashMap<Object, Integer>>();

		// handle case if CNF consists only of one literal
		if (n == 1) {
			if (cnf instanceof Literal) {
				Literal l = (Literal) cnf;
				if (l.positive) {
					map.put(l.var, 0);
				} else {
					map.put(l.var, 1);
				}
				res.add(map);
			} else {
				Literal l = getLiterals(cnf).get(0);
				if (l.positive) {
					map.put(l.var, 0);
				} else {
					map.put(l.var, 1);
				}
				res.add(map);
			}
			return res;
		}

		// handle case if CNF consists of more than one literal
		for (int i = 0; i != (1 << n); i++) {
			String binaryRep = Integer.toBinaryString(i);
			while (binaryRep.length() != n) {
				binaryRep = '0' + binaryRep;
			}
			for (int k = 0; k < n; k++) { // literals
				int val = Character.getNumericValue(binaryRep.charAt(k));
				Literal lit = literals.get(k);
				map.put(lit.var, val);
				continue;
			} // here, all literals have their value according to a row in a truth table
			Node[] clauses = cnf.getChildren();
			if (clauses != null) {
				for (int l = 0; l < clauses.length; l++) {
					Node clause = clauses[l];
					if (isFalseClause(clause, map)) { // check if every literal in clause is false
						res.add(map);
						map = new HashMap<Object, Integer>();
						break; // if one clause is invalid, the CNF is invalid
					}
				}
			} else if (n == 1) { // special case: explain constraint redundant which contains only one literal
				res.add(map);
				break;
			}
		}
		return res;
	}

	/**
	 * Checks if all literals in a clause have a false value assignment. If this is the case, the tested value
	 * assignment leads to a false conjunctive normal form.
	 * 
	 * @param clause the clause of check if it is false
	 * @param map a map which contains a mapping between a variable and its value assignment
	 * @return true, if all literals in a clause have a false value assignment. Else, return false
	 */
	private boolean isFalseClause(Node clause, HashMap<Object, Integer> map) {
		ArrayList<Literal> literals = getLiterals(clause);
		for (Literal lit : literals) {
			if (!lit.positive && map.get(lit.var).equals(0)) { // literal is 1, CNF cannot be false
				return false;
			}

			if (lit.positive && map.get(lit.var).equals(1)) { //// literal is 1, CNF cannot be false
				return false;
			}
		}
		return true;
	}
}