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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Stack;

//import org.eclipse.swt.graphics.Color;
import org.prop4j.Literal;
import org.prop4j.Node;

import Jakarta.util.Util;
import de.ovgu.featureide.fm.core.base.FeatureUtils;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * The class LTMS (logic truth maintenance system) uses BCP for managing logical implications. By recording proofs
 * for implications, explanations can be constructed.
 * 
 * @author "Ananieva Sofia"
 */
public class LTMS {

	/**
	 * Differentiates between different modes to explain. A mode can either belong to Redundancy, Dead Features
	 * or False-optional Features.
	 */
	public static enum ExplanationMode {
		Redundancy, DeadFeature, FalseOptionalFeature
	};

	/**
	 * The model to explain the defect from. Used to retrieve a feature from a respective literal.
	 */
	private IFeatureModel model;
	/**
	 * The explanation of a defect.
	 */
	private List<String> reason = new ArrayList<String>();
	/**
	 * The stack to collect unit-open clauses.
	 */
	private Stack<Node> stackOpenClause = new Stack<Node>();
	/**
	 * The hashMap for bookkeeping of reasons and antecedents for literals. Key = literal.var, value = class Bookkeeping
	 */
	private HashMap<Object, Bookkeeping> valueMap = new HashMap<Object, Bookkeeping>();
	/**
	 * The clause which is violated (all terms are bound to false).
	 */
	private Node violatedClause;
	/**
	 * The list which contains a literal of a respective feature from the redundant constraint.
	 */
	private ArrayList<Literal> featuresRedundantConstr = null; // the feature from the redundant constraint

	/**
	 * Weight strings which occur in every generated explanation for a defect while searching for the shortest explanation.
	 */
	HashMap<String, Integer> weightedExplanations = new HashMap<String, Integer>();

	/**
	 * Constructor is used if redundant constraints are explained.
	 * 
	 * @param oldModel the model without the redundant constraint
	 * @param map the valueMap which contains all literals from the conjunctive normal form and is which used
	 *            for bookkeeping (stores the name, reason, antecedents, premise and truth value of a literal)
	 * @param features the features from the redundant constraint
	 */
	public LTMS(IFeatureModel oldModel, HashMap<Object, Bookkeeping> map, ArrayList<Literal> features) {
		this(oldModel);
		valueMap = map;
		featuresRedundantConstr = features;
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
	 * Add explanation parts to member "reason" if not empty and unique.
	 * 
	 * @param s the explanation string to add to reason
	 */
	private void addToReasonListOptionally(String s) {
		if (!s.isEmpty() && !reason.contains(s)) {
			reason.add(s);
		}
	}

	/**
	 * Explains why a constraint is redundant. As soon as a clause gets violated, an explanation is generated.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @return String an explanation for the redundant constraint
	 * @throws IOException
	 */
	public List<String> explainRedundantConstraint(Node[] clauses, HashMap<Object, Integer> map) {
		reason.clear();
		// if initial truth values lead to a false clause, explain immediately
		if (isViolated(clauses)) {
			ArrayList<Literal> literalList = getLiterals(violatedClause);
			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				addToReasonListOptionally(tmpReason);
			}
			// remember first explanation strings in order to weight them later according their occurrences 
			for (String tmp : reason) {
				weightedExplanations.put(tmp, 1);
				weightExpl(reason, weightedExplanations, 1);
			}
			return reason;
		}
		// if we are here, propagated values via BCP lead to a false clause
		findOpenClauses(featuresRedundantConstr, clauses); // find first open clauses with initial truth value assumptions
		BCP(clauses);// true, if violation occured during BCP	
		return shortestExpl(clauses, map, null, ExplanationMode.Redundancy);
	}

	/**
	 * Explains why a feature if false optional. Sets value assignment of false-optional feature to false and propagate this value
	 * until a violation in any occurs.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @param falseoptional the literal-feature which is false-optional
	 * @param parent the literal-parent of the false optional feature
	 * @return String an explanation why the feature is false-optional
	 */
	public List<String> explainFalseOpsFeature(Node[] clauses, Literal falseoptional, Literal parent) {
		ArrayList<Literal> falsopts = new ArrayList<Literal>();
		falsopts.add(parent); 
		falsopts.add(falseoptional); 
		reason.clear();
		setTruthValToUnknown(clauses);
		valueMap.get(parent.var).value = 1; // set parent of false optional feature to true
		valueMap.get(parent.var).premise = true;
		valueMap.get(falseoptional.var).value = 0; // set false optional feature to false
		valueMap.get(falseoptional.var).premise = true;

		// if initial truth values lead to a false clause, explain immediately
		if (isViolated(clauses)) {
			ArrayList<Literal> literalList = getLiterals(violatedClause);
			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				addToReasonListOptionally(tmpReason);
			}
			// remember first explanation strings in order to weight them later according their occurrences 
			for (String tmp : reason) {
				weightedExplanations.put(tmp, 1);
				weightExpl(reason, weightedExplanations, 1);
			}
			return reason;
		}
		// if we are here, propagated values via BCP lead to a false clause
		findOpenClauses(falsopts, clauses); // find unit open clauses depending on initial truth values 
		BCP(clauses); // propagate values and find further unit open clauses
		return shortestExpl(clauses, null, falseoptional, ExplanationMode.FalseOptionalFeature);
	}

	/**
	 * Explains why a feature is dead. As soon as a violation in any clause occurs, an explanation is generated.
	 * 
	 * @param clauses the clauses of the conjunctive normal form of the feature model
	 * @param deadF the dead feature
	 * @param cond true if feature might be conditionally dead, else false
	 * @return String an explanation why the feature is dead
	 */
	public List<String> explainDeadFeature(Node[] clauses, Literal deadF) {
		ArrayList<Literal> deads = new ArrayList<Literal>();
		deads.add(deadF);
		reason.clear();
		setTruthValToUnknown(clauses);
		valueMap.get(deadF.var).value = 1;
		valueMap.get(deadF.var).premise = true;

		// if initial truth values lead to a false clause, explain immediately
		if (isViolated(clauses)) {
			ArrayList<Literal> literalList = getLiterals(violatedClause);
			for (Literal l : literalList) {
				String tmpReason = explainVariable(l);
				addToReasonListOptionally(tmpReason);
			}
			// remember first explanation strings in order to weight them later according their occurrences 
			for (String tmp : reason) {
				weightedExplanations.put(tmp, 1);
				weightExpl(reason, weightedExplanations, 1);
			}
			return reason;
		}
		findOpenClauses(deads, clauses);
		BCP(clauses);
		return shortestExpl(clauses, null, deadF, ExplanationMode.DeadFeature);
	}

	/**
	 * Generate all possible explanations and choose the shortest one. The length of an explanation
	 * is measured by the amount of lines it consists of. Every line represents a relationship within the
	 * feature model tree topology or a cross-tree constraint.
	 * 
	 * @param expl the first generated explanation
	 * @param clauses the clauses of the conjunctive normal form
	 * @param map the map which stores the initial values for features from the redundant constraint
	 * @return String the shortest explanation
	 */
	private List<String> shortestExpl(Node[] clauses, HashMap<Object, Integer> map, Literal explLit, ExplanationMode mode) {
		List<String> shortestExpl = (List<String>) ((ArrayList<String>) reason).clone(); // remember first explanation
		int allExpl = 1; // remember number of explanations

		// remember first explanation strings in order to weight them later according their occurrences 
		for (String tmp : shortestExpl) {
			weightedExplanations.put(tmp, 1);
		}
		while (!stackOpenClause.isEmpty()) { // generate explanations until stack with unit open clauses is empty

			// restore preconditions to start BCP algorithm again
			reason.clear();
			violatedClause = null;
			setTruthValToUnknown(clauses);

			switch (mode) {
			case Redundancy: // parameter map is expected not to be null
				for (Literal l : featuresRedundantConstr) {
					valueMap.get(l.var).value = map.get(l.var); // set value of feature from redundant constraint according to invalid redundant constraint
					valueMap.get(l.var).premise = true;
				}
				break;

			case DeadFeature: // explain dead feature, set its initial value to true
				valueMap.get(explLit.var).value = 1;
				valueMap.get(explLit.var).premise = true;
				break;

			case FalseOptionalFeature:// explain false-optional feature, set its initial value to false
				valueMap.get(explLit.var).value = 0;
				valueMap.get(explLit.var).premise = true;
				break;

			default:
				shortestExpl.add("unknown explanation mode");
				return shortestExpl;
			}
			BCP(clauses); // generate new explanation with remaining clauses in stack 
			if (!reason.isEmpty()) {
				allExpl++;

				// remember how often a certain string occurred in several explanations for the same defect
				for (String tmp : reason) {
					if (weightedExplanations.containsKey(tmp)) {
						weightedExplanations.put(tmp, weightedExplanations.get(tmp) + 1);
					} else {
						weightedExplanations.put(tmp, 1);
					}
				}
				if (reason.size() < shortestExpl.size()) { //remember only shortest explanation
					shortestExpl = (List<String>) ((ArrayList<String>) reason).clone();
				}
			}
		}
		// if we are here, shortest explanation is found
		weightExpl(shortestExpl, weightedExplanations, allExpl); // mark explanations parts within final explanation
		return shortestExpl;
	}

	/**
	 * Processes the shortest explanation and marks parts of an explanation which occur in every
	 * explanation (intersection) or are most common ones. Such explanation parts possess a high probability
	 * to trigger the defect to explain.
	 * 
	 * @param shortest the shortest explanation
	 * @param weighted the explanation parts to mark
	 * @param cnt the number of explanations
	 * @return the shortest explanation with marked explanation parts that occur most often
	 */
	public List<String> weightExpl(List<String> shortest, HashMap<String, Integer> weighted, int cntAllExpl) {

		// remove all explanation parts which are not part of the shortest explanation
		Iterator<String> it = weighted.keySet().iterator();
		while (it.hasNext()) {
			String expl = it.next();
			if (!shortest.contains(expl)) {
				it.remove();
			}
		}
		// get max number of occurences
		ArrayList<Integer> list = new ArrayList<Integer>();
		for (String key : weighted.keySet()) {
			list.add(weighted.get(key));
		}
		Iterator<String> it2 = weighted.keySet().iterator();
		while (it2.hasNext()) {
			String explMap = it2.next();
			for (ListIterator<String> itr = shortest.listIterator(); itr.hasNext();) {
				String explShortest = (String) itr.next(); // A => B
				if (explMap.equals(explShortest)) {
					int cntOccur = weighted.get(explMap);
					itr.set(explShortest + "$" + cntOccur + "/" + cntAllExpl);
					break;
				}
			}
		}
		return shortest;
	}

	/**
	 * Finds unit open clauses depending on the initial truth value assumptions of
	 * the features from the redundant constraint and pushes them to stack.
	 * 
	 * @param literal the literal from the redundant constraint whose value is initially set
	 * @param allClauses clauses of the conjunctive normal form
	 */
	private void findOpenClauses(ArrayList<Literal> literals, Node[] allClauses) {
		for (Literal l : literals) {
			boolean negated = (valueMap.get(l.var).value == 0);
			for (Node cnfclause : allClauses) {
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
	private boolean setValue(Literal literal, boolean negated, Node[] allClauses) {

		// propagate value of variable to be true or false
		valueMap.get(literal.var).value = literal.positive ? 1 : 0;

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
			if (evaluateValue(lit) == 0) {
				if (valueMap.get(lit.var).reason == null && valueMap.get(lit.var).premise == false) { // features from red. constraint can't have antecedents
					justify(lit, clause);// set reason and antecedent
				}
				continue;
			}
			return false;
		}
		violatedClause = clause; // remember violated clause for explanation
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
	 * Checks if a clause contains a not-literal.
	 * 
	 * @param neg representation of the opposite sign of a literal
	 * @param l the literal
	 * @param node a clause which may contain a not-literal
	 * @return true, if a clause contains not-literal. Else, return false
	 */
	private boolean hasNegTerm(boolean neg, Literal l, Node node) {
		ArrayList<Literal> literals = getLiterals(node);
		for (Literal lit : literals) {
			if (neg && !lit.positive && lit.var.toString().equals(l.var.toString())) {
				return true;
			}
			if (neg || !lit.positive || !lit.var.toString().equals(l.var.toString())) {
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
			switch (evaluateValue(lit)) {
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
	 * @param l the literal to evaluate the truth value for.
	 * @return Integer the Integer which represents the truth value of a term
	 */
	private int evaluateValue(Literal l) {
		if (!l.positive) {
			return this.negate(valueMap.get(l.var).value);
		}
		return valueMap.get(l.var).value;
	}

	/**
	 * Returns the truth value of a variable: true (1), false (0) or unknown (-1).
	 * 
	 * @param v the variable to evaluate the truth value for
	 * @return Integer which represents the truth value of a variable
	 */
	private int negate(int v) {
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
		while (!stackOpenClause.empty()) {
			Node openclause = stackOpenClause.pop();
			Literal l = isUnitOpen(openclause);
			if (l == null) {
				continue;
			}
			justify(l, openclause); //set reason and antecedents explanation
			if (setValue(l, !l.positive, cnfclauses)) { // set propagated value and push unit open clauses to stack
				continue;
			}

			// BCP is finished, all clauses are checked or a clause is violated
			ArrayList<Literal> literalsFromViolatedClause = getLiterals(violatedClause);
			ArrayList<Literal> literalsFromReason = getLiterals(valueMap.get(l.var).reason);

			// first, explain the violated clause and then start explaining from the current reason-clause
			if (!literalsFromViolatedClause.equals(literalsFromReason)) {
				for (Literal lit : literalsFromViolatedClause) {
					String varExpl = explainVariable(lit);
					addToReasonListOptionally(varExpl);
				}
			}
			explainValue(l);
			return false;
		}
		return true;
	}

	/**
	 * Returns an explanation why a variable has its truth value by iterating its antecedents
	 * and collecting their reasons. Only called to explain the BCP stack, not the violated clause.
	 * 
	 * @param l the literal to explain
	 * @return a string to explain a variables truth value
	 */
	private void explainValue(Literal l) {
		ArrayList<Literal> allAntencedents = new ArrayList<Literal>();
		allAntencedents.add(l);
		collectAntecedents(l, allAntencedents); //collect all variables together that contribute to this variable's value

		// explain relationship of every antecedent with the literal in focus (needed to find correct feature attribute)
		for (Literal v : allAntencedents) {
			String tmp = explainVariable(v);
			addToReasonListOptionally(tmp);

			// explain every antecedent from its reason in map 
			Node reasonFromMap = valueMap.get(v.var).reason;
			if (reasonFromMap != null) {
				Literal litFromMap = getLiteralFromMap(reasonFromMap, v);
				String explFromMap = explainVariable(litFromMap);
				addToReasonListOptionally(explFromMap);
			}
		}
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
					s += f.getName() + " alternative child of " + parentName;
				}
				// if parent is or, explain or relationship between all children
				else if (parent.getStructure().isOr()) {
					s += f.getName() + " or child of " + parentName;
				} else { // if parent is not "alt" or "or", then feature is mandatory or optional child
					s = featureName + (FeatureUtils.isMandatory(f) ? " mandatory" : "") + " child of " + parent;
				}
			}
		}
		//if attribute is root, print "ROOT" as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Root) {
			s = "ROOT " + l.var.toString();
		}
		// if attribute is CONSTRAINT, print origin constraint as explanation only
		if (l.getSourceAttribute() == Literal.FeatureAttribute.Constraint) {
			s = "Constraint " + (FeatureUtils.getConstraint(model, l.getSourceIndex())).toString();
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
	 * Returns a literal from a node.
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
}