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
import java.util.Arrays;
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
 * and its boolean constraint propagation (BCP).
 * 
 * @author "Ananieva Sofia"
 */
public class Redundancy {
	
	/**
	 * The hashMap for bookkeeping of reasons and antecedents for literals. Key = literal.var, value = class Bookkeeping
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
	 * Explains why a constraint is redundant. Assumes values for features of the redundant constraint
	 * which lead to a false formula of the redundant constraint and propagates this values until a violation
	 * in a clause occurs.
	 * 
	 * @param oldModel the feature model without the redundant constraint
	 * @param redundantConstraint the redundant constraint
	 */
	public String explain(IFeatureModel oldModel, IFeatureModel newModel, IConstraint redundantConstraint) {
		model = oldModel; // the model without the redundant constraint
		setNewModel(newModel);
		featRedundantConstr = getLiterals(redundantConstraint.getNode());
		featRedundantConstr = new ArrayList<Literal>(new LinkedHashSet<Literal>(featRedundantConstr)); // remove duplicates from list
		String reason = "Constraint is redundant, because: \n,"; // last comma is used as delimiter in order to remove duplicates 
		Node node = NodeCreator.createNodes(oldModel, true).toCNF(); 
		Node redundantConstr = redundantConstraint.getNode().toCNF();
		ArrayList<HashMap<Object, Integer>> values = getFeatureValues(featRedundantConstr.size(), redundantConstr, featRedundantConstr); // arraylist of hashmaps with values for false cnf
		Node[] clauses = node.getChildren();

		for (HashMap<Object, Integer> map : values) {
			reason = reason.trim() + "\n";
			setTruthValueToUnknown(clauses); //(re)set all literal values to -1

			for (Literal l : featRedundantConstr) {
				valueMap.get(l.var).value = map.get(l.var);// get literal from origin map and set its value according to false cnf
				valueMap.get(l.var).premise = true;
			}
			LTMS ltms = new LTMS(model, valueMap, featRedundantConstr);
			reason += ltms.explainRedundant(clauses, map).trim() + "\n";
		}
		if (reason.isEmpty()) {
			return "No explanation possible";
		} else {		
			reason = prepare(reason);
			return reason;
		}
	}
	
	/**
	 * Prepare string for tool tip. Remove duplicates and unnecessary characters.
	 * 
	 * @param The string to prepare
	 * @return String the string with the explanation for a redundant constraint
	 */
	private String prepare(String s) {	
		s = removeDup(s); // remove duplicates
		int lastChar = s.lastIndexOf(",");
		s = s.substring(0, lastChar); // remove last comma from explanation
		s = s.substring(1, 35) + s.substring(39); // remove comma which was only used as delimiter to remove duplicates
		return s; 
	}
	
	/**
	 * Remove duplicate explanation parts which are separated by ","
	 * 
	 * @param The string to remove the duplicates from
	 * @return String the string without duplicates
	 */
	private String removeDup(String s) {
	    return new LinkedHashSet<String>(Arrays.asList(s.split(","))).toString();
	}

	/**
	 * Sets the model with the new redundant constraint.
	 * 
	 * @param model the model with the new constraint
	 */
	private void setNewModel(IFeatureModel model) {
		newModel = model;
	}

	/**
	 * Gets the model with the new constraint. Used for tooltips to get the correct constraint index.
	 * 
	 * @return the model with the new constraint
	 */
	public static IFeatureModel getNewModel() {
		return newModel;
	}

	/**
	 * Returns a list which contains the literals of a given node.
	 * 
	 * @param node the node which contains the literals
	 * @return a list which contains the literals
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
	 * @return a list which contains a mapping between a variable and its value assignment
	 */
	private ArrayList<HashMap<Object, Integer>> getFeatureValues(int n, Node cnf, ArrayList<Literal> literals) {
		HashMap<Object, Integer> map = new HashMap<Object, Integer>();
		ArrayList<HashMap<Object, Integer>> res = new ArrayList<HashMap<Object, Integer>>();

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
						break; // if one clause is false, cnf is false
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
	 * Checks if all terms in a clause have a false value assignment. If this is the case, the tested value
	 * assignment leads to a false conjunctive normal form.
	 * 
	 * @param clause the clause of check if it is false
	 * @param map a map which contains a mapping between a variable and its value assignment
	 * @return true, if all terms in a clause have a false value assignment. Else, return false
	 */
	private boolean isFalseClause(Node clause, HashMap<Object, Integer> map) {
		ArrayList<Literal> literals = getLiterals(clause);
		for (Literal lit : literals) {
			if (!lit.positive && map.get(lit.var).equals(0)) { // literal is 1, cnf cannot be false
				return false;
			}

			if (lit.positive && map.get(lit.var).equals(1)) { //// literal is 1, cnf cannot be false
				return false;
			}
		}
		return true;
	}
}