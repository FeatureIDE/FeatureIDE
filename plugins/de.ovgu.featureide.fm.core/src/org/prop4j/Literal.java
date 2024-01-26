/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package org.prop4j;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.UnaryOperator;

import de.ovgu.featureide.fm.core.editing.NodeCreator;

/**
 * A variable or negated variable.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class Literal extends Node implements Cloneable {

	public Object var;

	public boolean positive;

	/**
	 * Creates a new positive literal.
	 *
	 * @param var contained variable
	 */
	public Literal(Object var) {
		this(var, true);
	}

	/**
	 * Creates a new literal.
	 *
	 * @param var contained variable
	 * @param positive whether the variable is positive or negated
	 */
	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}

	protected Literal(Literal oldLiteral) {
		var = oldLiteral.var;
		positive = oldLiteral.positive;
	}

	public void flip() {
		positive = !positive;
	}

	@Override
	public boolean isConjunctiveNormalForm() {
		return true;
	}

	@Override
	public boolean isDisjunctiveNormalForm() {
		return true;
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return clone();
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		return this;
	}

	@Override
	protected Node clausifyDNF(boolean simplify) {
		return this;
	}

	@Override
	public Node simplify() {
		return this;
	}

	@Override
	public Node flatten() {
		return this;
	}

	@Override
	public Node deMorgan() {
		return this;
	}

	@Override
	protected List<Node> replaceFeature(String feature, String replaceWithFeature, List<Node> list) {
		if (var.equals(feature)) {
			var = replaceWithFeature;
			list.add(this);
		}
		return list;
	}

	@Override
	public void modifyFeatureNames(UnaryOperator<String> f) {
		var = f.apply(String.valueOf(var));
	}

	@Override
	public Literal clone() {
		return new Literal(this);
	}

	@Override
	public int hashCode() {
		return Objects.hashCode(var) * (positive ? 31 : 37);
	}

	@Override
	public boolean equals(Object node) {
		if (this == node) {
			return true;
		}
		if (!(node instanceof Literal)) {
			return false;
		}
		final Literal other = (Literal) node;
		return (positive == other.positive) && Objects.equals(var, other.var);
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		if (var == NodeCreator.varFalse) {
			return !positive;
		}
		if (var == NodeCreator.varTrue) {
			return positive;
		}
		final Boolean value = map.get(var);
		if (value == null) {
			throw new IllegalArgumentException("No value for " + String.valueOf(var));
		}
		return positive == value;
	}

	@Override
	protected <T extends Collection<String>> T getContainedFeatures(T containedFeatures) {
		containedFeatures.add(String.valueOf(var));
		return containedFeatures;
	}

	@Override
	protected <T extends Collection<Literal>> T getLiterals(T literals) {
		literals.add(this);
		return literals;
	}

	@Override
	protected <T extends Collection<Object>> T getVariables(T variables) {
		variables.add(var);
		return variables;
	}

	@Override
	public int getMaxDepth() {
		return 1;
	}

}
