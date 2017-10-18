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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.And;
import org.prop4j.Literal;
import org.prop4j.Node;
import org.prop4j.NodeWriter;
import org.prop4j.Not;
import org.prop4j.Or;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * TODO description
 *
 * @author Alexander Knueppel
 */
public class TseitinConverter extends NNFConverter {

	private int number = 0;
	private final Set<String> auxVariables = new HashSet<String>();

	private IFeature addClause(IFeature top, String name) {
		final IFeature clause = factory.createFeature(top.getFeatureModel(), name);
		clause.getStructure().setAbstract(true);
		clause.getStructure().setOr();
		clause.getStructure().setMandatory(true);
		top.getStructure().addChild(clause.getStructure());

		return clause;
	}

	private void addTseitinVariable(IFeature top, String name, boolean mandatory) {
		final IFeature var = factory.createFeature(top.getFeatureModel(), name);
		var.getStructure().setAbstract(true);
		var.getStructure().setMandatory(mandatory);
		top.getStructure().addChild(var.getStructure());
	}

	@Override
	protected void createAbstractSubtree(IFeature top, List<Node> nodes) {
//		int i = 0;
//		addClause(top, "x0");
//		for(Node node : nodes) {
//			IFeature clause = addClause(top, "clause" + (i++));
//
//			//System.out.println(node);
//
//			for(Node child : node.getChildren()) {
//				String name = "";
//				if(auxVariables.contains(child.getContainedFeatures().get(0))) {
//					//name = child.getContainedFeatures().get(0);
//				} else {
//					name = child.getContainedFeatures().get(0) + "_" + i;
//					addTerminalAndConstraints(clause, child, name, preserve);
//				}
//				//name = child.getContainedFeatures().get(0) + "_" + i;
//				//addTerminalAndConstraints(clause, child, name, preserve);
//				//System.out.println(clause + ", " + child + ", " + name);
//			}
//		}

		final IFeature clause = addClause(top, "Tseitin");

		for (final String var : auxVariables) {
			addTseitinVariable(clause, var, (var.equals("x0")) ? true : false);
		}

		super.createAbstractSubtree(top, nodes);
	}

	/**
	 * Creates tseitin cnf and returns a list of clauses
	 */
	@Override
	public List<Node> preprocess(IConstraint constraint) {
		Node node = constraint.getNode().clone();

		final String[] supported = new String[] { "!", " && ", " || ", NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol,
			NodeWriter.noSymbol, NodeWriter.noSymbol };
		node = node.eliminateNotSupportedSymbols(supported);

		final List<Node> result = new LinkedList<Node>();

		for (Node encoded : tseitinEncoding(constraint.getFeatureModel(), node, "x" + (number))) {
			encoded = encoded.toCNF();
			if (encoded instanceof And) {
				result.addAll(Arrays.asList(encoded.getChildren()));
			} else {
				result.add(encoded);
			}
		}

		return result;
	}

	private List<Node> tseitinEncoding(IFeatureModel fm, Node node, String var) {
		final List<Node> tseitinEncoding = new ArrayList<Node>();

		// Unary node
		if (node.getContainedFeatures().size() == 1) {
			tseitinEncoding.add(node);
			return tseitinEncoding;
		}

		auxVariables.add(var);

		if (node instanceof Not) {
			// TODO: not correct...
			tseitinEncoding.addAll(tseitinEncoding(fm, node.getChildren()[0], "x" + (++number)));
			tseitinEncoding.add(new Or(var, "x" + (number)));
			tseitinEncoding.add(new Or(new Not(var), new Not("x" + (number))));
		} else if (node instanceof Or) {
			final List<Node> tmp = new ArrayList<Node>();
			for (final Node child : node.getChildren()) {
				if (child.getContainedFeatures().size() == 1) {
					tmp.add(child);
				} else {
					tmp.add(new Literal("x" + (++number)));
					tseitinEncoding.addAll(tseitinEncoding(fm, child, "x" + number));
				}

			}
			tseitinEncoding.add(new Or(new Not(var), new Or(tmp.toArray())));
			for (final Node y : tmp) {
				tseitinEncoding.add(new Or(var, new Not(y)));
			}
		} else {
			final List<Node> tmp = new ArrayList<Node>();
			for (final Node child : node.getChildren()) {
				if (child.getContainedFeatures().size() == 1) {
					tmp.add(child);
				} else {
					tmp.add(new Literal("x" + (++number)));
					tseitinEncoding.addAll(tseitinEncoding(fm, child, "x" + number));
				}
			}
			final List<Node> neg = new ArrayList<Node>();
			for (final Node y : tmp) {
				neg.add(new Not(y));
			}
			tseitinEncoding.add(new Or(var, new Or(neg.toArray())));
			for (final Node y : tmp) {
				tseitinEncoding.add(new Or(new Not(var), y));
			}
		}

		return tseitinEncoding;
	}

}
