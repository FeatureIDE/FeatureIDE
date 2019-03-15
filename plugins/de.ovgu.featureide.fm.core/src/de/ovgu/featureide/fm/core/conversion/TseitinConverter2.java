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

/**
 * TODO description
 *
 * @author Alexander Knueppel
 * @author Sebastian Krieter
 */
public class TseitinConverter2 {

	private int number = 0;
	private final Set<String> auxVariables = new HashSet<>();

	public Node convert(Node node) {
		auxVariables.clear();

		final String[] supported = new String[] { "!", " && ", " || ", NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol, NodeWriter.noSymbol,
			NodeWriter.noSymbol, NodeWriter.noSymbol };
		node = node.eliminateNotSupportedSymbols(supported);

		final List<Node> result = new LinkedList<>();

		final String var = "x" + (number);
		for (final Node encoded : tseitinEncoding(node, var)) {
			result.addAll(Arrays.asList(encoded.toRegularCNF().getChildren()));
		}
		result.add(new Or(new Literal(var)));

		return new And(result);
	}

	public Set<String> getAuxVariables() {
		return auxVariables;
	}

	private List<Node> tseitinEncoding(Node node, String var) {
		final List<Node> tseitinEncoding = new ArrayList<>();

		// Unary node
		if (node.getContainedFeatures().size() == 1) {
			tseitinEncoding.add(node);
			return tseitinEncoding;
		}

		auxVariables.add(var);

		if (node instanceof Not) {
			node = Node.deMorgan(node);
		}

		if (node instanceof Or) {
			final List<Node> tmp = new ArrayList<>();
			for (final Node child : node.getChildren()) {
				if (child.getContainedFeatures().size() == 1) {
					tmp.add(child);
				} else {
					tmp.add(new Literal("x" + (++number)));
					tseitinEncoding.addAll(tseitinEncoding(child, "x" + number));
				}
			}
			tseitinEncoding.add(new Or(new Not(var), new Or(tmp.toArray())));
			for (final Node y : tmp) {
				tseitinEncoding.add(new Or(var, new Not(y)));
			}
		} else {
			final List<Node> tmp = new ArrayList<>();
			for (final Node child : node.getChildren()) {
				if (child.getContainedFeatures().size() == 1) {
					tmp.add(child);
				} else {
					tmp.add(new Literal("x" + (++number)));
					tseitinEncoding.addAll(tseitinEncoding(child, "x" + number));
				}
			}
			final List<Node> neg = new ArrayList<>();
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
