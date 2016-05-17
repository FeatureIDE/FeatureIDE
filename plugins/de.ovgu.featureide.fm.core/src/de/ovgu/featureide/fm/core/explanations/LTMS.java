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
package de.ovgu.featureide.fm.core.explanations;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Set;
import java.util.Stack;

import org.prop4j.Literal;
import org.prop4j.Node;

import Jakarta.util.Util;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * A logic truth maintenance system (LTMS) is used for managing logical implications. By recording proofs
 * for the implications, explanations can be constructed.
 * 
 * @author "Ananieva Sofia"
 */
public class LTMS {

	private boolean explRed = false; // true, if a redundant constraint shall be explained
	private int cntLength = 0; // count the parts of an explanation in order to select the shortest explanation
	private IFeatureModel model;
	private String reason = "";
	private Stack<Node> stackOpenClause = new Stack<Node>(); // stack for unit open clauses
	private HashMap<Object, Bookkeeping> valueMap = new HashMap<Object, Bookkeeping>(); // bookkeeping of reasons and antecedents for literals 
	private HashMap<Integer, String> allExplanations = new HashMap<Integer, String>(); // storing all explanations. key = length, value = explanation
	private Node violatedClause; // the clause whose terms are all false
	private ArrayList<Literal> featFromRedConstr = null; // the feature from the redundant constraint
	private Node openclause = null;
	private Literal deadFeature;

	/**
	 * Constructor is used if redundant constraints are explained.
	 * 
	 * @param oldModel the model without the redundant constraint
	 * @param map the valueMap which contains all literals from the conjunctive normal form and is which used
	 *            for bookkeeping (stores the name, reason, antecedents, premise and truth value of a literal)
	 * @param features the features from the redundant constraint
	 */
	public LTMS(IFeatureModel oldModel, HashMap<Object, Bookkeeping> map, ArrayList<Literal> features) {
		model = oldModel;
		valueMap = map;
		featFromRedConstr = features;
	}

	/**
	 * Constructor is used if dead or false-optional features are explained.
	 * 
	 * @param newModel the model with the constraint which leads to dead feature(s)
	 * @param map the valueMap which is used for bookkeeping
	 */
	public LTMS(IFeatureModel newModel) {
		model = newModel;
	}

	/**
	 * Explains why a constraint is redundant. As soon as a clause gets violated, an explanation is generated.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @return String an explanation for the redundant constraint
	 */
	public String explainRedundant(Node[] clauses, HashMap<Object, Integer> map) {
		explRed = true;
		reason = "";

		// if initial truth values lead to a false clause, explain immediately
		if (isViolated(clauses)) {
			ArrayList<Literal> literalList = getLiterals(getViolatedClause());

			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				if (!reason.contains(tmpReason)) {
					reason = reason + tmpReason + "\n";
				}
			}
			return reason;
		}

		// if we are here, propagated values via BCP lead to a false clause
		setInitialOpenClauses(featFromRedConstr, clauses); // find first open clauses with initial truth value assumptions
		if (!BCP(clauses)) { // true, if violation occured during BCP
			return shortestExplanation(reason, clauses, map, null);
		}
		return shortestExplanation(reason, clauses, map, null);
	}

	/**
	 * Explains why a feature if false optional. Sets value assignment of false-optional feature to false and propagate this value
	 * until a violation in any occurs.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @param falseoptional the literal-feature which is false-optional
	 * @return String an explanation why the feature is false-optional
	 */
	public String explainFalseOps(Node[] clauses, Literal falseoptional) {
		ArrayList<Literal> falsopts = new ArrayList<Literal>();
		falsopts.add(falseoptional);
		reason = "";
		setTruthValToUnknown(clauses);
		valueMap.get(falseoptional.var).value = 0;
		valueMap.get(falseoptional.var).premise = true;

		// if initial truth values lead to a false clause, explain immediately
		if (isViolated(clauses)) {
			ArrayList<Literal> literalList = getLiterals(getViolatedClause());

			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				if (!reason.contains(tmpReason)) {
					reason = reason + tmpReason;
				}
			}
			return reason;
		}

		// if we are here, propagated values via BCP lead to a false clause
		setInitialOpenClauses(falsopts, clauses);
		if (!BCP(clauses)) {
			return shortestExplanation(reason, clauses, null, falseoptional);
		}
		return shortestExplanation(reason, clauses, null, falseoptional);
	}

	/**
	 * Explains why a feature is dead. As soon as a violation in any clause occurs, an explanation is generated.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @param deadF the dead feature
	 * @param cond true if feature might be conditionally dead, else false
	 * @return String an explanation why the feature is dead
	 */
	public String explainDead(Node[] clauses, Literal deadF) {
		deadFeature = deadF;
		reason = "";
		setTruthValToUnknown(clauses);
		valueMap.get(deadF.var).premise = true;

		if (!set(deadF, false, clauses) || !BCP(clauses)) {
			return shortestExplanation(reason, clauses, null, deadF);
		}
		return shortestExplanation(reason, clauses, null, deadF);
	}

	/**
	 * Generate all possible explanations and choose the shortest one. The length of an explanation
	 * is measured by the amount of parts (is child, is root, is constraint) it consists of.
	 * 
	 * @param expl the first generated explanation
	 * @param clauses the clauses of the conjunctive normal form
	 * @param map the map which stores the intial values for features from the redundant constraint
	 * @return String the shortest explanation
	 */
	private String shortestExplanation(String expl, Node[] clauses, HashMap<Object, Integer> map, Literal explLit) {
		final long meanEnd = System.currentTimeMillis();
		System.out.println("Erste Erklärung: " + meanEnd + " Millisek.");

		String shortestExpl = "";
		allExplanations.put(cntLength, expl); // remember first explanation
		while (!stackOpenClause.isEmpty()) {
			reason = "";
			cntLength = 0;
			setTruthValToUnknown(clauses);

			if (explRed == true) { // explain redundant features, set their initial values according to invalid formula of redundant constraint
				for (Literal l : featFromRedConstr) {
					valueMap.get(l.var).value = map.get(l.var);// get literal from origin map and set its value according to false cnf
					valueMap.get(l.var).premise = true;
				}
			} else {
				if (deadFeature != null) { // explain dead feature, set its initial value to true
					valueMap.get(explLit.var).value = 1;
				} else { // explain false-optional feature, set its initial value to false
					valueMap.get(explLit.var).value = 0;
				}
				valueMap.get(explLit.var).premise = true;
			}
			BCP(clauses); // generate new explanation with remaining clauses in stack 
			if (cntLength == 0) { // don't take empty reason as explanation 
				continue;
			}
			if (allExplanations.get(cntLength) != null) { // don't replace explanation with another one having the same length
				continue;
			}
			allExplanations.put(cntLength, reason);
		}
		// if we are here, all explanations have been generated and stored in a hashmap (key = length, value = explanation)
		Set<Integer> keySet = allExplanations.keySet();
		ArrayList<Integer> list = new ArrayList<Integer>(keySet);
		Collections.sort(list);
		int minLength = list.get(0);
		shortestExpl = allExplanations.get(minLength);
		return shortestExpl;
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
	 * Returns a specified literal from (another) node
	 * 
	 * @param node the node which contains the literal
	 * @param l the literal with the same name as the literal to return
	 * @return the specified literal
	 */
	private Literal getLiteralFromMap(Node node, Literal l) {
		Literal res = null;
		if (node instanceof Literal) {
			Literal lit = (Literal) node;
			if (lit.var.toString().equals(l.var.toString()))
				res = lit;
			return res;
		}

		Node[] childs = node.getChildren();
		if (childs != null) {
			for (Node child : childs) {
				res = getLiteralFromMap((child), l);
				if (res != null) {
					return res;
				}
			}
		}
		return res;
	}

	/**
	 * Finds the very first unit open clauses depending on the initial truth value assumptions of
	 * the features from the redundant constraint and pushes them to stack.
	 * 
	 * @param literal the literal from the redundant constraint whose value is initially set
	 * @param allClauses clauses of the conjunctive normal form
	 */
	private void setInitialOpenClauses(ArrayList<Literal> literal, Node[] allClauses) {
		boolean negated = false;
		for (Literal l : literal) {
			if (valueMap.get(l.var).value == 0) {
				negated = true;
			}
			for (Node cnfclause : allClauses) {

				// check for every assumed value if there are unit open clauses
				if (!hasNegTerm(!negated, l, cnfclause)) {
					continue;
				}
				if (isUnitOpen(cnfclause) != null && !stackOpenClause.contains(cnfclause)) {
					stackOpenClause.push(cnfclause);
					continue;
				}
			}
		}
	}

	/**
	 * Sets the value of a literal depending on its negation in the unit open clause. Finds new unit open
	 * clauses and pushes them to stack.
	 * 
	 * @param literal the literal whose value is set using boolean constraint propagation
	 * @param negated true, if the literal is negated in the open clause. Else, false
	 * @return true, if the value of a literal is set without violating a clause. Else, return false
	 */
	private boolean set(Literal literal, boolean negated, Node[] allClauses) {

		// propagate value of variable to be true or false
		if (literal.positive == true) {
			valueMap.get(literal.var).value = 1;
		} else {
			valueMap.get(literal.var).value = 0;
		}

		// for each clause in all clauses of the cnf that contains not this-literal
		for (Node cnfclause : allClauses) {
			if (!hasNegTerm(!negated, literal, cnfclause)) { //if true is returned, unit-open is checked and then violation
				continue;
			}

			// if we are here, we may have found a unit open clause
			if (isUnitOpen(cnfclause) != null) {
				stackOpenClause.push(cnfclause);
				continue;
			}
			if (!isViolated(cnfclause)) {
				continue;
			}
			return false;
		}
		return true;
	}

	/**
	 * Checks if a clause is violated (all terms are false).
	 * 
	 * @param clause the clause to check
	 * @return true, if the clause is violated. Else, return false
	 */
	private boolean isViolated(Node clause) {

		// truth values of all terms must be false
		ArrayList<Literal> literals = getLiterals(clause);
		for (Literal lit : literals) {
			if (eval3(lit) == 0) {

				if (valueMap.get(lit.var).reason == null && valueMap.get(lit.var).premise == false) { // features from red. constraint can't have antecedents
					justify(lit, clause);// set reason and antecedent
				}
				continue;
			}
			return false;
		}
		setViolatedClause(clause); // remember violated clause for explanation
		return true;
	}

	/**
	 * Checks if a single clause in the conjunctive normal form is violated (all terms are false).
	 * 
	 * @param n the clauses to check
	 * @return true, if the clause is violated. Else, return false
	 */
	private boolean isViolated(Node[] n) {
		for (Node cnfclause : n) {
			if (!isViolated(cnfclause)) {
				continue;
			}
			return true; // clause is violated, all terms are 0
		}
		return false; // clause is not violated
	}

	/**
	 * Sets the violated clause.
	 * 
	 * @param clause the violated clause
	 */
	private void setViolatedClause(Node clause) {
		violatedClause = clause;
	}

	/**
	 * Returns the violated clause.
	 * 
	 * @return the violated clause.
	 */
	private Node getViolatedClause() {
		return violatedClause;
	}

	/**
	 * Checks if a clause contains a not-literal for explaining redundant constraints.
	 * 
	 * @param neg representation of the opposite sign of a literal
	 * @param l the literal
	 * @param node a clause which may contain a not-literal
	 * @return true, if a clause contains not-literal. Else, return false
	 */
	private boolean hasNegTerm(boolean neg, Literal l, Node node) {
		ArrayList<Literal> literals = getLiterals(node);
		for (Literal lit : literals) {

			if (neg && !lit.positive && lit.var.toString().equals(l.var.toString())) { //guidsl compares id's of literals with same name, not working for featureIDE
				return true;
			}

			if (neg || !lit.positive || !lit.var.toString().equals(l.var.toString())) { //!!guidsl compares id's of literals, not working for featureIDE!!
				continue;
			}
			return true;
		}
		return false;
	}

	/**
	 * Checks if a clause is unit open. In a unit open clause, all terms are false except
	 * for one term whose truth value is unknown.
	 * 
	 * @param clause the clause to check if it is unit open
	 * @return the literal whose value is unknown
	 */
	private Literal isUnitOpen(Node clause) {
		Literal openTerm = null;
		ArrayList<Literal> literals = getLiterals(clause);
		for (Literal lit : literals) {
			switch (eval3(lit)) {
			case 0: { // do nothing
				break;
			}
			case 1: { //can't be open because term is true and therefore the clause
				return null;
			}
			case -1: { // -1: is unit open
				if (openTerm == null) {
					openTerm = lit; //remember first open term
					break;
				}
				return null; // more than one term unknown - can't be open
			}
			}
		}
		// if we get this far, this is a unit open clause or a unsatisfied clause, else, null is returned
		return openTerm;
	}

	/**
	 * Checks if a term is true, false or unknown.
	 * 
	 * @param l the literal
	 * @return int representation of a terms value
	 */
	private int eval3(Literal l) {
		if (!l.positive) {
			return this.negate3(valueMap.get(l.var).value);
		}
		return valueMap.get(l.var).value;
	}

	/**
	 * Returns the truth value of a term: true (1), false (0) or unknown (-1).
	 * 
	 * @param v
	 * @return
	 */
	private int negate3(int v) {
		switch (v) {
		case 1: {
			return 0;
		}
		case 0: {
			return 1;
		}
		case -1: {
			return -1;
		}
		}
		Util.fatalError((String) ("Unknown value: " + v));
		return -3; // will never get here
	}

	/**
	 * Sets the reason and the antecedents (antecedents: all terms, which are in the same clause as this
	 * literal and are false)
	 * 
	 * @param l the literal to set its reason and antecedents
	 * @param clause the clause of the literal
	 */
	private void justify(Literal l, Node clause) {
		valueMap.get(l.var).reason = clause;
		valueMap.get(l.var).antecedents = new ArrayList<Literal>();

		ArrayList<Literal> literals = getLiterals(clause);
		for (Literal lit : literals) {

			if (lit.var.toString().equals(l.var.toString())) {
				continue;
			}
			valueMap.get(l.var).antecedents.add(lit); // all variables from same clause added to antecedents which are not this variable
		}
	}

	/**
	 * Core of the logic truth maintenance system. The BCP algorithm maintains a stack of unit open clauses.
	 * Changes the unknown assignment of a literals truth value to true and sets its reason and antecedents. Finds
	 * new unit open clauses and pushes them to stack. Whenever it encounters a violated clause, it signals a
	 * contradiction.
	 * 
	 * @param cnfclauses the clauses of the conjunctive normal form of a feature model
	 * @return true, if all unit open clauses have been processed and no violated clause have been encountered
	 */
	private boolean BCP(Node[] cnfclauses) {
		String tmpReason = "";
		while (!stackOpenClause.empty()) {
			openclause = stackOpenClause.pop();
			Literal l = isUnitOpen(openclause);
			if (l == null) {
				continue;
			}
			justify(l, openclause); //set reason and antecedents explanation
			if (set(l, !l.positive, cnfclauses)) { // set propagated value and push unit open clauses to stack
				continue;
			}

			// BCP is finished, all clauses are checked or a clause is violated
			ArrayList<Literal> explLitViolatedClause = getLiterals(getViolatedClause());
			ArrayList<Literal> explLitReason = getLiterals(valueMap.get(l.var).reason);

			// first, explain the violated clause and then start explaining from the current reason-clause
			if (!explLitViolatedClause.equals(explLitReason)) {
				for (Literal lit : explLitViolatedClause) {
					tmpReason = "";
					tmpReason = explainVariable(lit);
					if (!reason.contains(tmpReason)) {
						reason = reason + tmpReason + "\n";
					} else if (!tmpReason.equals("")) {
						cntLength--;
					}
				}
			}
			if (explLitReason.size() == 1) {//if only 1 element in list
				tmpReason = "";
				tmpReason = explainValue(l);
				if (!reason.contains(tmpReason)) {
					reason = reason + tmpReason + "\n";
				}
				return false; // inconsistency
			}
			tmpReason = "";
			tmpReason = explainValue(l);
			if (!reason.contains(tmpReason)) {
				reason = reason + tmpReason + "\n";
			}
			return false;
		}
		return true;
	}

	/**
	 * Returns an explanation why a variable has its truth value by iterating its antecedents
	 * and collecting their reasons. Only called to explain the BCP stack, not the violated clause.
	 * 
	 * @param l the literal to explain from the violated clause
	 * @return a string to explain a variables truth value
	 */
	private String explainValue(Literal l) {
		ArrayList<Literal> allAntencedents = new ArrayList<Literal>();
		allAntencedents.add(l);
		collectAntecedents(l, allAntencedents); //collect all variables together that contribute to this variable's value
		String result = "";

		for (Literal v : allAntencedents) { // explain every collected antecedent
			String tmp = explainVariable(v);
			if (!result.contains(tmp) && !reason.contains(tmp)) {
				result += tmp + "\n";
			} else if (!tmp.equals("")) {
				cntLength--; // if the same explanation has been generated again and length has been incremented, reduce length
			}

			// explain every antecedent from its unit open clause 
			Node reasonFromMap = valueMap.get(v.var).reason;
			if (reasonFromMap != null) {
				Literal litFromMap = getLiteralFromMap(reasonFromMap, v);
				String explFromMap = explainVariable(litFromMap);
				if (!result.contains(explFromMap) && !reason.contains(explFromMap)) {
					// result contains an explanation for the BCP stack, reason contains an explanation for the violated clause 
					result += explFromMap + "\n";
				} else if (!tmp.equals("") && tmp.equals(explFromMap)) {
					cntLength--; // if the same explanation has been generated again and length has been incremented, reduce length
				}
			}
		}
		return result;
	}

	/**
	 * Forms a union of all antecedents.
	 * 
	 * @param l the literal whose antecedents shall be collected
	 * @param antecedents a list which is used to collect the antecedents.
	 */
	private void collectAntecedents(Literal l, ArrayList<Literal> antecedents) {
		if (valueMap.get(l.var).antecedents == null) {
			return;
		}
		for (Literal antecendent : valueMap.get(l.var).antecedents) { // collect antecedents recursively
			if (antecedents.contains(antecendent))
				continue;
			antecedents.add(antecendent);
			collectAntecedents(antecendent, antecedents);
		}
	}

	/**
	 * Explains a truth value of a literal. Uses an enumeration to choose between explaining a
	 * relationship to parent or a cross-tree constraint.
	 * 
	 * @param l the literal to explain
	 * @return String with explanation for the literal
	 */
	private String explainVariable(Literal l) {
		String s = "";
		IFeature f = FeatureUtils.getFeatureTable(model).get(l.var);

		// if attribute is UP, explain relationship to parent
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Up) {
			cntLength++; // increase length of explanation
			if (FeatureUtils.getParent(f) != null) {
				IFeature parent = FeatureUtils.getParent(f);
				String parentName = parent.getName();
				String featureName = f.getName();

				// if parent is alternative, explain alternative relationship between all children
				if (parent.getStructure().isAlternative()) {
				//	Iterable<IFeature> children = FeatureUtils.getChildren(parent);
				//	for (IFeature child : children) {
				//		s += child + " alternative child of " + parentName + ", \n";
						s += f.getName() + " alternative child of " + parentName + ", ";

				//	}
				}
				// if parent is or, explain or relationship between all children
				else if (parent.getStructure().isOr()) {
				//	Iterable<IFeature> children = FeatureUtils.getChildren(parent);
				//	for (IFeature child : children) {
				//		s += child + " or child of " + parentName + ", \n";
					s += f.getName() + " or child of " + parentName + ", ";
				//	}
				}

				else { // if parent is not "alt" or "or", then feature is mandatory or optional child
					s = featureName + (FeatureUtils.isMandatory(f) ? " mandatory" : "") + " child of " + parent + ", ";
				}
			}
		}
		//if attribute is root, print "ROOT" as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Root) {
			cntLength++; // increase length of explanation
			s = "ROOT " + l.var.toString() + ", ";
		}

		// if attribute is CONSTRAINT, print origin constraint as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Constraint) {
			cntLength++; // increase length of explanation
			s = "Constraint " + (FeatureUtils.getConstraint(model, l.getSourceIndex())).toString() + ", ";
		}
		return s;
	}

	/**
	 * Sets the truth value of every literal in the conjunctive normal form to -1 (unknown)
	 * 
	 * @param clausesFromCNF clauses of the conjunctive normal form
	 */
	private void setTruthValToUnknown(Node[] clausesFromCNF) {
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
}
