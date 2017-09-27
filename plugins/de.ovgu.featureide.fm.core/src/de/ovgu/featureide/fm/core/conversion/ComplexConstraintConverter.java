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
package de.ovgu.featureide.fm.core.conversion;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.ConstraintAttribute;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * TODO description
 *
 * @author Alexander
 */
public class ComplexConstraintConverter {

	/* Feature model factory */
	private IFeatureModelFactory factory;
	/* Working feature model */
	protected IFeatureModel fm;

	public enum Option {
		COHERENT, REMOVE_RDUNDANCY
	}

	/**
	 * Checks whether a given node is either a requires- or an excludes-constraint.
	 *
	 * @param node
	 * @return true if node is a simple constraint. False otherwise.
	 */
	public static boolean isSimple(Node node) {
		if (node.getContainedFeatures().size() == 1) {
			return false;
		}

		final Node cnf = node.toCNF();
		if ((cnf.getChildren().length == 1) && (cnf.getContainedFeatures().size() == 2)) {
			final Node clause = cnf.getChildren()[0];
			if (clause instanceof Or) {
				final Node f1 = clause.getChildren()[0];
				final Node f2 = clause.getChildren()[1];

				return ((f1 instanceof Literal) && !((Literal) f1).positive) || ((f2 instanceof Literal) && !((Literal) f2).positive);
			}
		}
		return false;
	}

	/**
	 * Checks whether a given node is neither a requires- nor an excludes-constraint.
	 *
	 * @param node
	 * @return true if node is a complex constraint. False otherwise.
	 */
	public static boolean isComplex(Node node) {
		return !ComplexConstraintConverter.isSimple(node);
	}

	/**
	 * Checks whether a given node is a (hidden) composition of requires- and excludes-constraints.
	 *
	 * @param node
	 * @return true if node consists of a number of simple constraints. False otherwise.
	 */
	public static boolean isPseudoComplex(Node node) {
		final Node cnf = node.toCNF();

		if ((cnf instanceof Or) || (cnf instanceof Literal)) {
			return isSimple(node);
		}

		boolean result = true;
		for (final Node child : cnf.getChildren()) {
			result &= isSimple(child);
		}

		return result;
	}

	/**
	 * Checks whether there exist only constraints that can be refactored trivially.
	 *
	 * @param node
	 * @return true if no construction of an abstract subtree is necessary. False otherwise.
	 */
	public static boolean trivialRefactoring(List<Node> nodes) {
		for (final Node node : nodes) {
			if (!isPseudoComplex(node)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Checks whether there exist only constraints that can be refactored trivially.
	 *
	 * @param fm
	 * @return true if no construction of an abstract subtree is necessary. False otherwise.
	 */
	public static boolean trivialRefactoring(final IFeatureModel fm) {
		final List<Node> nodes = new LinkedList<Node>();
		for (final IConstraint c : fm.getConstraints()) {
			nodes.add(c.getNode());
		}
		return ComplexConstraintConverter.trivialRefactoring(nodes);
	}

	/**
	 * Eliminates complex constraints according to a given strategy.
	 *
	 * @param fm
	 * @return
	 */
	public IFeatureModel convert(IFeatureModel model, IConverterStrategy converter, Option... options) {
		// check if model is valid
		if (model == null) {
			throw new IllegalArgumentException("Invalid feature model.");
		}

		if (converter == null) {
			throw new IllegalArgumentException("Invalid converter.");
		}

		boolean coherent = false;
		boolean removeRedundncy = false;

		for (final Option o : options) {
			if (o.equals(Option.COHERENT)) {
				coherent = true;
			}
			if (o.equals(Option.REMOVE_RDUNDANCY)) {
				removeRedundncy = true;
			}
		}

		// Work with a clone
		fm = model.clone();
		factory = FMFactoryManager.getFactory(fm);

		// Basic cleaning
		if (removeRedundncy && !prepare()) {
			return fm;
		}

		// Identify trivial refactorings
		refactorPseudoComplexConstraints();

		// Get list of complex clauses and remove them from the model
		final List<IConstraint> complexConstraints = pruneComplexConstraints();

		// Minimize constraints
		final List<Node> minComplexNodes = new ArrayList<Node>();
		for (final IConstraint c : complexConstraints) {
			final List<Node> nodes = converter.preprocess(c);

			for (final Node node : nodes) {
				final Node minNode = minimize(node);

				if (ComplexConstraintConverter.isSimple(minNode)) {
					fm.addConstraint(factory.createConstraint(fm, minNode));
				} else if (minNode instanceof And) {
					final List<Node> conj = new LinkedList<Node>();
					for (final Node sub : minNode.getChildren()) {
						if (ComplexConstraintConverter.isSimple(sub)) {
							fm.addConstraint(factory.createConstraint(fm, sub));
						} else {
							conj.add(sub);
						}
						minComplexNodes.add(new And(conj.toArray()));
					}
				} else {
					minComplexNodes.add(minNode);
				}
			}
		}

		if (minComplexNodes.isEmpty()) {
			return fm;
		}

		final IFeatureModel res = converter.convert(fm, minComplexNodes, coherent);
		return res;
	}

	/**
	 *
	 * @param clause
	 * @return
	 */
	protected Node minimize(Node clause) {
		// TODO minimize complex clauses
		return clause;
	}

	/**
	 * Removes tautologies and redundant constraints. If the feature model is a void model or unsatisfiable then a simple contradicting feature model will be
	 * created.
	 */
	protected boolean prepare() {
		final FeatureModelAnalyzer analyzer = fm.getAnalyser();

		analyzer.calculateFeatures = true;
		analyzer.calculateConstraints = true;
		analyzer.calculateRedundantConstraints = true;
		analyzer.calculateTautologyConstraints = true;

		analyzer.analyzeFeatureModel(null);
		final List<IConstraint> toRemove = new LinkedList<IConstraint>();

		for (final IConstraint c : fm.getConstraints()) {
			final ConstraintAttribute attribute = c.getConstraintAttribute();

			if ((attribute == ConstraintAttribute.REDUNDANT) || (attribute == ConstraintAttribute.TAUTOLOGY)) {
				toRemove.add(c);
			}
		}

		for (final IConstraint c : toRemove) {
			fm.removeConstraint(c);
		}
		return true;
	}

	/**
	 * Splits up a complex constraint into simple constraints if possible.
	 */
	protected void refactorPseudoComplexConstraints() {
		final List<IConstraint> pseudoComplexConstraints = new LinkedList<IConstraint>();
		for (final IConstraint c : fm.getConstraints()) {
			if (ComplexConstraintConverter.isPseudoComplex(c.getNode().clone())) {
				pseudoComplexConstraints.add(c);
			}
		}

		for (final IConstraint c : pseudoComplexConstraints) {
			final Node cnf = c.getNode().toCNF();
			if (cnf instanceof And) {
				for (final Node clause : cnf.getChildren()) {
					fm.addConstraint(factory.createConstraint(fm, clause));
				}
			} else {
				fm.addConstraint(factory.createConstraint(fm, cnf));
			}
			fm.removeConstraint(c);
		}
	}

	/**
	 * Collects and removes all complex constraints from the feature model.
	 *
	 * @return List of complex constraints
	 */
	protected List<IConstraint> pruneComplexConstraints() {
		final List<IConstraint> complexConstraints = new LinkedList<IConstraint>();

		for (final IConstraint c : fm.getConstraints()) {
			if (ComplexConstraintConverter.isComplex(c.getNode())) {
				complexConstraints.add(c);
			}
		}

		for (final IConstraint c : complexConstraints) {
			fm.removeConstraint(c);
		}

		return complexConstraints;
	}
}
