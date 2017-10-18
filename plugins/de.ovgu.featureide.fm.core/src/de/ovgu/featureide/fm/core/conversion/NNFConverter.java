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
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.prop4j.And;
import org.prop4j.Implies;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureModelFactory;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;

/**
 * @brief Converter using negation normal form.
 *
 * @author Alexander Knueppel
 */
public class NNFConverter implements IConverterStrategy {

	/** Feature model factory */
	protected IFeatureModelFactory factory;
	/** Working feature model */
	protected IFeatureModel fm;
	/** Preserving configuration semantics */
	protected boolean preserve = false;
	/** Running number for naming */
	private int suffix = 0;
	/** Naming scheme */
	protected Map<Class<?>, String> naming = new HashMap<Class<?>, String>();
	protected String topName = "Subtree";
	protected String newRootName = "NewRoot";

	protected static int subtree = 0;

	/**
	 * Constructor
	 */
	public NNFConverter() {
		// continues number + level
		naming.put(And.class, "AND%d_%d");
		// continues number + level
		naming.put(Or.class, "OR%d_%d");
		// feature name + continues number + level
		naming.put(Literal.class, "%s_%d_%d");
		// feature name + continues number + level
		naming.put(Not.class, "NOT_%s_%d_%d");
	}

	/**
	 * Generates new name if feature name is already taken
	 *
	 * @param name
	 * @return
	 */
	private String getName(String name) {
		if (fm.getFeature(name) == null) {
			return name;
		}

		int i = 0;
		while (fm.getFeature(name + "_" + i) != null) {
			i++;
		}

		return name + "_" + i;
	}

	/**
	 * Returns an appropriate name for feature
	 *
	 * @param node
	 * @param level
	 * @return
	 */
	private String getName(Node node, int level) {
		final List<Object> args = new ArrayList<Object>();
		if ((node instanceof Literal) || (node instanceof Not)) {
			args.add(node.getContainedFeatures().get(0));
		}
		args.addAll(Arrays.asList(new Object[] { suffix, level }));
		return getName(String.format(naming.get(node.getClass()), args.toArray()));
	}

	/**
	 * Restructures root if needed.
	 *
	 * @param fm Feature model
	 * @param name Name of new root
	 */
	protected void restructureRoot(String name) {
		if (!fm.getStructure().getRoot().isAnd()) {
			final IFeature newRoot = factory.createFeature(fm, name);
			newRoot.getStructure().addChild(fm.getStructure().getRoot());
			newRoot.getStructure().setMandatory(true);
			fm.getStructure().setRoot(newRoot.getStructure());
			fm.addFeature(newRoot);
		}
	}

	/**
	 * Adds a new element under root.
	 *
	 * @param fm Feature model
	 * @param name Name of element
	 * @return The top element for further actions
	 */
	protected IFeature prepareTopElement(String name) {
		final IFeature top = factory.createFeature(fm, name);
		fm.getStructure().getRoot().addChild(top.getStructure());
		top.getStructure().changeToAnd();
		top.getStructure().setAbstract(true);
		top.getStructure().setMandatory(true);
		fm.addFeature(top);
		return top;
	}

	/**
	 * Adds a requires-constraint between two feature.
	 *
	 * @param f1
	 * @param f2
	 */
	protected void addRequires(String f1, String f2) {
		final Node requires = new Implies(new Literal(f1), new Literal(f2));
		fm.addConstraint(factory.createConstraint(fm, requires));
	}

	/**
	 * Adds an excludes-constraint between two features.
	 *
	 * @param f1
	 * @param f2
	 */
	protected void addExcludes(String f1, String f2) {
		final Node excludes = new Implies(new Literal(f1), new Not(new Literal(f2)));
		fm.addConstraint(factory.createConstraint(fm, excludes));
	}

	/**
	 * Adds an equivalent structure and constraints to a feature model according to a given set of propositional formulas.
	 *
	 * @param top
	 * @param nodes
	 */
	protected void createAbstractSubtree(IFeature top, List<Node> nodes) {
		createAbstractSubtree(top, nodes, 0);
	}

	/**
	 *
	 * @param top
	 * @param nodes
	 * @param level
	 */
	private void createAbstractSubtree(IFeature top, List<Node> nodes, int level) {
		// Increment suffix for every new modeled constraint
//		if(level == 1) {
//			System.out.println("Next subtree: " + (++subtree));
//		}
		for (final Node node : nodes) {
			if (level == 1) {
				suffix++;
			}

			final String name = getName(node, level);

			// Terminal feature
			if ((node.getContainedFeatures().size() == 1) && !(node instanceof And) && !(node instanceof Or)) {
				final IFeature feature = factory.createFeature(top.getFeatureModel(), name);
				feature.getStructure().setAbstract(true);
				feature.getStructure().setMandatory(true);
				top.getStructure().addChild(feature.getStructure());
				fm.addFeature(feature);
				if (!(node instanceof Not) && ((Literal) node).positive) {
					addRequires(name, node.getContainedFeatures().get(0));
					if (preserve) {
						addRequires(node.getContainedFeatures().get(0), name);
					}
				} else {
					addExcludes(name, node.getContainedFeatures().get(0));
				}

				continue;
			}

			// Non-Terminal feature: either And or Or
			final IFeature feature = factory.createFeature(top.getFeatureModel(), name);// "c_" + (suffix++));
			feature.getStructure().setAbstract(true);
			feature.getStructure().setMandatory(true);
			if (node instanceof And) {
				feature.getStructure().setAnd();
			} else {
				feature.getStructure().setOr();
			}

			// Recursive call
			createAbstractSubtree(feature, Arrays.asList(node.getChildren()), level + 1);
			top.getStructure().addChild(feature.getStructure());
			fm.addFeature(feature);
		}

	}

	@Override
	public IFeatureModel convert(IFeatureModel fm, List<Node> nodes, boolean preserve) {
		this.fm = fm.clone();
		factory = FMFactoryManager.getFactory(fm);
		this.preserve = preserve;

		if (nodes.isEmpty()) {
			return this.fm;
		}

		restructureRoot(getName(newRootName));
		final IFeature top = prepareTopElement(getName(topName));
		createAbstractSubtree(top, nodes);

		simplify(top);

		return this.fm;
	}

	@Override
	public List<Node> preprocess(IConstraint constraint) {
		final List<Node> elements = new LinkedList<Node>();
		Node node = constraint.getNode().clone();

		final String[] supported = new String[] { "!", " && ", " || ", NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol,
			NodeWriter.noSymbol, NodeWriter.noSymbol };
		node = node.eliminateNotSupportedSymbols(supported);

		node = propagateNegation(node, false);

		elements.add(node);
		return elements;
	}

	/**
	 * Decrease size of subtree through merging abstract features
	 *
	 * @param top
	 */
	protected void simplify(IFeature top) {
		if (top instanceof And) {
			// TODO
		}
	}

	/**
	 *
	 * @param node
	 * @param negated
	 * @return
	 */
	private Node propagateNegation(Node node, boolean negated) {
		if (node instanceof Not) {
			negated = !negated;
			return propagateNegation(node.getChildren()[0], negated);
		} else if ((node instanceof And) || (node instanceof Or)) {
			final List<Node> nodelist = new ArrayList<Node>();
			for (final Node tmp : node.getChildren()) {
				nodelist.add(propagateNegation(tmp, negated));
			}

			if (node instanceof And) {
				if (negated) {
					return new Or(nodelist.toArray());
				} else {
					return new And(nodelist.toArray());
				}
			} else {
				if (negated) {
					return new And(nodelist.toArray());
				} else {
					return new Or(nodelist.toArray());
				}
			}
		}

		// node is an atom
		if (negated) {
			return new Not(node);
		}

		return node;
	}

}
