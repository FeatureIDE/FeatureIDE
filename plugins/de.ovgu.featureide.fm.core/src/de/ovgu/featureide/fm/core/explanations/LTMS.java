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
import java.util.HashMap;
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

	private String reason = "";
	private Stack<Node> unitOpenClause = new Stack<Node>(); // stack for unit open clauses
	private HashMap<Object, Bookkeeping> valueMap = new HashMap<Object, Bookkeeping>(); //hashmap for bookkeeping of reasons and antecedents for literals 
	private Node violatedClause; // the clause whose values are all false after a truth value has been propagated via BCP
	private IFeatureModel model;
	private ArrayList<Literal> featFromRedConstr = null;
	private boolean explRed = false;
	private Node openclause = null;
	private Literal deadFeature; // the dead feature to explain
	//	private Literal condDead; //antecedent which appears in list with different signs, needed to detect cond. dead features 
	private Node[] cnfclauses;
	ArrayList<Literal> preDead = new ArrayList<Literal>(); // previously dead features, needed to detect cond. dead features

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
	 * Constructor is used if dead features are explained.
	 * 
	 * @param newModel the model with the constraint which leads to dead feature(s)
	 * @param map the valueMap which is used for bookkeeping
	 */
	public LTMS(IFeatureModel newModel, HashMap<Object, Bookkeeping> map) {
		model = newModel;
		valueMap = map;
	}

	/**
	 * Explains why a constraint is redundant. As soon as a clause gets violated, an explanation is generated.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @return String an explanation for the redundant constraint
	 */
	public String explainRedundant(Node[] clauses) {
		explRed = true;
		reason = "";
		if (isViolated(clauses)) { // true, if initial truth values lead to a false clause -> explain immediately
			ArrayList<Literal> literalList = getLiterals(getViolatedClause());

			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				if (!reason.contains(tmpReason)) {
					reason = reason + tmpReason + "\n\n";
				}
			}
			return reason;
		}

		// if we are here, propagated values via BCP lead to a false clause
		setFirstOpenClauses(featFromRedConstr, clauses); // find first open clauses with initial truth value assumptions
		if (!BCP(clauses)) { // true, if violation occured during BCP
			return reason;
		}
		return reason;
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
		cnfclauses = clauses;
		reason = "";

		setTruthValToUnknown(clauses);
		if (!set(deadF, false, clauses) || !BCP(clauses)) {
			return reason;
		}
		return reason;
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
		cnfclauses = clauses;
		reason = "";

		setTruthValToUnknown(clauses);
		valueMap.get(falseoptional.var).value = 0;
		setFirstOpenClauses(falsopts, clauses);
		if (!BCP(clauses)) { // true, if violation occured during BCP
			return reason;
		}
		return reason;
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
	private void setFirstOpenClauses(ArrayList<Literal> literal, Node[] allClauses) {
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
				if (isUnitOpen(cnfclause) != null && !unitOpenClause.contains(cnfclause)) {
					unitOpenClause.push(cnfclause);
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
				unitOpenClause.push(cnfclause);
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
			
				if (neg || !lit.positive || !lit.var.toString().equals(l.var.toString())){ //!!guidsl compares id's of literals, not working for featureIDE!!
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
		while (!unitOpenClause.empty()) {
			openclause = unitOpenClause.pop();
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

			// first, explain violated clause and then begin explaining from current reason-clause. In some cases, both clauses are the same
			if (!explLitViolatedClause.equals(explLitReason)) {
				for (Literal lit : explLitViolatedClause) {
					tmpReason = explainVariable(lit);
					if (!reason.contains(tmpReason)) {
						reason = reason + tmpReason + "\n";
					}
				}
			}

			for (Literal lit : explLitReason) {
				if (explLitReason.size() == 1) {//if only 1 element in list
					tmpReason = explainValue(lit);
					if (!reason.contains(tmpReason)) {
						reason = reason + tmpReason + "\n";
					}
					return false; // inconsistency
				}

				tmpReason = explainValue(lit);
				if (!reason.contains(tmpReason)) {
					reason = reason + tmpReason + "\n";
				}
				return false; // inconsistency
			}
		}
		return true;
	}

	/**
	 * Returns an explanation why a variable has its truth value by iterating its antecedents
	 * and collecting their reasons.
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
			if (explRed == true) {
				
				// explain every antecedent from its unit open clause while setting its value
				Node reason = valueMap.get(v.var).reason;
				if (reason != null) {
					Literal litFromMap = getLiteralFromMap(reason, v);
					String tmp = explainVariable(litFromMap);
					if (!result.contains(tmp)) {
						result += tmp + "\n";
					}
				}
			}
			String tmp = explainVariable(v);
			if (!result.contains(tmp) && !reason.contains(tmp)) {
				result += tmp + "\n";
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
			if (FeatureUtils.getParent(f) != null) {
				IFeature parent = FeatureUtils.getParent(f);
				String parentName = parent.getName();
				String featureName = f.getName();

				// if parent is alternative, explain alternative relationship between all children
				if (parent.getStructure().isAlternative()) {
					Iterable<IFeature> children = FeatureUtils.getChildren(parent);
					for (IFeature child : children) {
						s += child + " alternative child of " + parentName + ", ";
					}
				}
				// if parent is or, explain or relationship between all children
				else if (parent.getStructure().isOr()) {
					Iterable<IFeature> children = FeatureUtils.getChildren(parent);
					for (IFeature child : children) {
						s += child + " or child of " + parentName + ", ";
					}
				}

				else { // if parent is not "alt" or "or", then feature is mandatory or optional child
					s = featureName + (FeatureUtils.isMandatory(f) ? " mandatory" : "") + " child of " + parent + ", ";
				}
			}
		}
		//if attribute is root, print "ROOT" as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Root) {
			s = "ROOT " + l.var.toString();
		}

		// if attribute is CONSTRAINT, print origin constraint as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Constraint) {
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
