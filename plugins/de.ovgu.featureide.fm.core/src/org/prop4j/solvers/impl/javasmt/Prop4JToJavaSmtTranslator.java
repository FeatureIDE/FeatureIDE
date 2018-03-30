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
package org.prop4j.solvers.impl.javasmt;

import java.util.Arrays;
import java.util.HashMap;

import org.prop4j.And;
import org.prop4j.Constant;
import org.prop4j.DoubleType;
import org.prop4j.Equal;
import org.prop4j.Equals;
import org.prop4j.Function;
import org.prop4j.GreaterEqual;
import org.prop4j.GreaterThan;
import org.prop4j.Implies;
import org.prop4j.IntegerType;
import org.prop4j.LessEqual;
import org.prop4j.LessThan;
import org.prop4j.Literal;
import org.prop4j.LongType;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.Or;
import org.prop4j.Term;
import org.prop4j.Variable;
import org.prop4j.solver.ISolver;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.RationalFormula;
import org.sosy_lab.java_smt.api.RationalFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

/**
 * Class containing functions that are used to translate the formulas created by prop4j to be used with java smt.
 *
 * @author Joshua Sprey
 */
public class Prop4JToJavaSmtTranslator {

	protected SolverContext currentContext;
	protected FormulaManager currentFormulaManager;
	protected BooleanFormulaManager currentBooleanFormulaManager;
	protected IntegerFormulaManager currentIntegerFormulaManager;
	protected RationalFormulaManager currentRationalFormulaManager;
	protected HashMap<String, NumeralFormula> variables = new HashMap<>();
	protected boolean isPrincess = false;
	protected ISolver solver;

	public Prop4JToJavaSmtTranslator(SolverContext context, ISolver solver) {
		setContext(context);
		this.solver = solver;
	}

	public void setContext(SolverContext context) {
		currentContext = context;
		currentFormulaManager = context.getFormulaManager();
		currentBooleanFormulaManager = currentFormulaManager.getBooleanFormulaManager();
		currentIntegerFormulaManager = currentFormulaManager.getIntegerFormulaManager();
		if (context.getSolverName() != Solvers.PRINCESS) { // Princess does not support Rationals
			isPrincess = false;
			currentRationalFormulaManager = currentFormulaManager.getRationalFormulaManager();
		} else {
			isPrincess = true;
		}
	}

	public BooleanFormula getFormula(Node node) {
		final BooleanFormula formula = nodeToFormula(node);
		return formula;
	}

	private BooleanFormula nodeToFormula(Node node) {
		if (node instanceof Not) {
			return handleNotNode((Not) node);
		} else if (node instanceof Or) {
			return handleOrNode((Or) node);
		} else if (node instanceof And) {
			return handleAndNode((And) node);
		} else if (node instanceof Equals) {
			return handleEqualsNode((Equals) node);
		} else if (node instanceof Implies) {
			return handleImpliesNode((Implies) node);
		} else if (node instanceof Literal) {
			return handleLiteralNode((Literal) node);
		} else if (node instanceof LessThan) {
			return handleLessThanNode((LessThan) node);
		} else if (node instanceof GreaterThan) {
			return handleGreaterThanNode((GreaterThan) node);
		} else if (node instanceof LessEqual) {
			return handleLessEqualNode((LessEqual) node);
		} else if (node instanceof GreaterEqual) {
			return handleGreaterEqualNode((GreaterEqual) node);
		} else if (node instanceof Equal) {
			return handleEqualNode((Equal) node);
		} else {
			throw new RuntimeException("The nodes of type: " + node.getClass() + " are not supported by JavaSmt.");
		}
	}

	private BooleanFormula handleAndNode(And node) {
		final BooleanFormula[] childs = new BooleanFormula[node.getChildren().length];
		for (int i = 0; i < childs.length; i++) {
			childs[i] = nodeToFormula(node.getChildren()[i]);
		}
		return currentBooleanFormulaManager.and(childs);
	}

	private BooleanFormula handleEqualNode(Equal node) {
		final NumeralFormula leftTerm = termToFormula(node.leftTerm);
		final NumeralFormula rightTerm = termToFormula(node.rightTerm);
		if (((leftTerm instanceof RationalFormula) || (rightTerm instanceof RationalFormula)) && !isPrincess) {
			return currentRationalFormulaManager.equal(leftTerm, rightTerm);
		} else {
			return currentIntegerFormulaManager.equal((IntegerFormula) leftTerm, (IntegerFormula) rightTerm);
		}
	}

	private BooleanFormula handleGreaterEqualNode(GreaterEqual node) {
		final NumeralFormula leftTerm = termToFormula(node.leftTerm);
		final NumeralFormula rightTerm = termToFormula(node.rightTerm);
		if (((leftTerm instanceof RationalFormula) || (rightTerm instanceof RationalFormula)) && !isPrincess) {
			return currentRationalFormulaManager.greaterOrEquals(leftTerm, rightTerm);
		} else {
			return currentIntegerFormulaManager.greaterOrEquals((IntegerFormula) leftTerm, (IntegerFormula) rightTerm);
		}
	}

	private BooleanFormula handleLessEqualNode(LessEqual node) {
		final NumeralFormula leftTerm = termToFormula(node.leftTerm);
		final NumeralFormula rightTerm = termToFormula(node.rightTerm);
		if (((leftTerm instanceof RationalFormula) || (rightTerm instanceof RationalFormula)) && !isPrincess) {
			return currentRationalFormulaManager.lessOrEquals(leftTerm, rightTerm);
		} else {
			return currentIntegerFormulaManager.lessOrEquals((IntegerFormula) leftTerm, (IntegerFormula) rightTerm);
		}
	}

	private BooleanFormula handleGreaterThanNode(GreaterThan node) {
		final NumeralFormula leftTerm = termToFormula(node.leftTerm);
		final NumeralFormula rightTerm = termToFormula(node.rightTerm);
		if (((leftTerm instanceof RationalFormula) || (rightTerm instanceof RationalFormula)) && !isPrincess) {
			return currentRationalFormulaManager.greaterThan(leftTerm, rightTerm);
		} else {
			return currentIntegerFormulaManager.greaterThan((IntegerFormula) leftTerm, (IntegerFormula) rightTerm);
		}
	}

	private BooleanFormula handleLessThanNode(LessThan node) {
		final NumeralFormula leftTerm = termToFormula(node.leftTerm);
		final NumeralFormula rightTerm = termToFormula(node.rightTerm);
		if (((leftTerm instanceof RationalFormula) || (rightTerm instanceof RationalFormula)) && !isPrincess) {
			return currentRationalFormulaManager.lessThan(leftTerm, rightTerm);
		} else {
			return currentIntegerFormulaManager.lessThan((IntegerFormula) leftTerm, (IntegerFormula) rightTerm);
		}
	}

	private BooleanFormula handleLiteralNode(Literal node) {
		final String variable = "" + node.var.toString();
		if (node.positive) {
			return currentBooleanFormulaManager.makeVariable(variable);
		} else {
			return currentBooleanFormulaManager.not(currentBooleanFormulaManager.makeVariable(variable));
		}
	}

	private BooleanFormula handleImpliesNode(Implies node) {
		final BooleanFormula leftChild = nodeToFormula(node.getChildren()[0]);
		final BooleanFormula rightChild = nodeToFormula(node.getChildren()[1]);
		return currentBooleanFormulaManager.implication(leftChild, rightChild);
	}

	private BooleanFormula handleEqualsNode(Equals node) {
		final BooleanFormula leftChild = nodeToFormula(node.getChildren()[0]);
		final BooleanFormula rightChild = nodeToFormula(node.getChildren()[1]);
		return currentBooleanFormulaManager.equivalence(leftChild, rightChild);
	}

	private BooleanFormula handleOrNode(Or node) {
		final BooleanFormula[] childs = new BooleanFormula[node.getChildren().length];
		for (int i = 0; i < childs.length; i++) {
			childs[i] = nodeToFormula(node.getChildren()[i]);
		}
		return currentBooleanFormulaManager.or(childs);
	}

	private BooleanFormula handleNotNode(Not notNode) {
		if (notNode.getChildren()[0] instanceof Node) {
			final BooleanFormula childFormula = nodeToFormula(notNode.getChildren()[0]);
			return currentBooleanFormulaManager.not(childFormula);
		} else {
			final BooleanFormula literal = nodeToFormula(notNode.getChildren()[0]);
			return currentBooleanFormulaManager.not(literal);
		}
	}

	private NumeralFormula termToFormula(Term term) {
		if (term instanceof Constant<?>) {
			final Constant<?> constant = (Constant<?>) term;
			return handleConstant(constant);
		} else if (term instanceof Variable<?>) {
			final Variable<?> variable = (Variable<?>) term;
			return handleVariable(variable);
		} else if (term instanceof Function) {
			return handleFunction((Function) term);
		} else {
			throw new RuntimeException("The given term is not supported by JavaSMT: " + term.getClass());
		}

	}

	private NumeralFormula handleFunction(Function function) {
		final NumeralFormula[] childs = new NumeralFormula[function.terms.length];
		for (int i = 0; i < childs.length; i++) {
			childs[i] = termToFormula(function.terms[i]);
		}
		if (isPrincess) {
			// Princess does not support rational therefore everything should be integer formula an save to cast.
			final IntegerFormula leftChild = (IntegerFormula) childs[0];
			final IntegerFormula rightChild = (IntegerFormula) childs[1];
			switch (function.type) {
			case Function.ADDITION:
				if (function.terms.length == 2) {
					return currentIntegerFormulaManager.add(leftChild, rightChild);
				} else {
					return currentIntegerFormulaManager.sum(Arrays.asList((IntegerFormula[]) childs));
				}
			case Function.SUBSTRACT:
				return currentIntegerFormulaManager.subtract(leftChild, rightChild);
			case Function.MODULO:
				return currentIntegerFormulaManager.modulo(leftChild, rightChild);
			case Function.MULTIPLY:
				return currentIntegerFormulaManager.multiply(leftChild, rightChild);
			case Function.NEGATE:
				return currentIntegerFormulaManager.negate(leftChild);
			case Function.DIVISION:
				return currentIntegerFormulaManager.divide(leftChild, rightChild);
			default:
				throw new RuntimeException("The given function is not supported by JavaSMT: " + function.type);
			}
		} else {

			switch (function.type) {
			case Function.ADDITION:
				if (function.terms.length == 2) {
					return currentRationalFormulaManager.add(childs[0], childs[1]);
				} else {
					return currentRationalFormulaManager.sum(Arrays.asList(childs));
				}
			case Function.SUBSTRACT:
				return currentRationalFormulaManager.subtract(childs[0], childs[1]);
			case Function.MODULO:
				return currentRationalFormulaManager.modulo(childs[0], childs[1]);
			case Function.MULTIPLY:
				return currentRationalFormulaManager.multiply(childs[0], childs[1]);
			case Function.NEGATE:
				return currentRationalFormulaManager.negate(childs[0]);
			case Function.DIVISION:
				return currentRationalFormulaManager.divide(childs[0], childs[1]);
			default:
				throw new RuntimeException("The given function is not supported by JavaSMT: " + function.type);
			}
		}

	}

	private NumeralFormula handleVariable(Variable<?> variable) {
		if ((variable.getType() instanceof DoubleType) && !isPrincess) {
			final NumeralFormula variableFormula = currentRationalFormulaManager.makeVariable(variable.getValue());
			variables.put(variable.toString(), variableFormula);
			return variableFormula;
		} else {
			final NumeralFormula variableFormula = currentIntegerFormulaManager.makeVariable(variable.getValue());
			variables.put(variable.toString(), variableFormula);
			return variableFormula;
		}
	}

	private NumeralFormula handleConstant(Constant<?> constant) {
		if (constant.getValue() instanceof IntegerType) {
			final IntegerType integerType = (IntegerType) constant.getValue();
			return currentIntegerFormulaManager.makeNumber(integerType.getValue());
		} else if (constant.getValue() instanceof LongType) {
			final LongType longType = (LongType) constant.getValue();
			return currentIntegerFormulaManager.makeNumber(longType.getValue());
		} else {
			final DoubleType doubleType = (DoubleType) constant.getValue();
			if (!isPrincess) {
				return currentRationalFormulaManager.makeNumber(doubleType.getValue());
			} else {
				throw new UnsupportedOperationException("Princess does not support constants from type: Double");
			}
		}
	}

	public HashMap<String, NumeralFormula> getVariables() {
		return variables;
	}

}
