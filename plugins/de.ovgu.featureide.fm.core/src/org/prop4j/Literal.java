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
package org.prop4j;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.impl.FeatureStructure;
import de.ovgu.featureide.fm.core.explanations.Explanation;

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
	 * Annotates each literal of a formula with an attribute for explanation.
	 * 
	 * @author Sofia Ananieva
	 * @author Timo G&uuml;nther
	 */
	public enum Origin {
		/** Denotes an unknown origin. */
		UNDEFINED,
		/** Denotes that the literal's origin is a {@link FeatureStructure#getChildren() child feature}. */
		CHILD,
		/** Denotes that the literal's origin is the {@link FeatureStructure#getParent() parent feature}. */
		PARENT,
		/** Denotes that the literal's origin is the {@link FeatureStructure#isRoot() root feature}. */
		ROOT,
		/** Denotes that the literal's origin is a {@link IConstraint constraint}. */
		CONSTRAINT
	};

	/**
	 * <p>
	 * Encodes the origin.
	 * Stores which {@link Origin type of origin} the literal has (using its {@link Origin#ordinal() ordinal}).
	 * Additionally, if the type is a {@link Origin#CONSTRAINT constraint}, its index in the feature model is stored (using its bitwise complement).
	 * </p>
	 * 
	 * <p>
	 * This information is necessary for generating {@link Explanation explanations}.
	 * </p>
	 */
	public int origin;

	/**
	 * Creates a new positive literal.
	 * @param var contained variable
	 */
	public Literal(Object var) {
		this(var, true);
	}

	/**
	 * Creates a new literal.
	 * @param var contained variable
	 * @param positive whether the variable is positive or negated
	 */
	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}

	/**
	 * Creates a new positive literal.
	 * @param var contained variable
	 * @param origin origin of the literal
	 * @throws IllegalArgumentException if the origin is a {@link Origin#CONSTRAINT constraint},
	 * in which case {@link #Literal(Object,int)} should be used
	 */
	public Literal(Object var, Origin origin) throws IllegalArgumentException {
		this(var, true, origin);
	}

	/**
	 * Creates a new positive literal.
	 * @param var contained variable
	 * @param constraintIndex the index of the origin constraint in the feature model
	 */
	public Literal(Object var, int constraintIndex) {
		this(var, true, constraintIndex);
	}

	/**
	 * Creates a new literal.
	 * @param var contained variable
	 * @param positive whether the variable is positive or negated
	 * @param origin origin of the literal
	 * @throws IllegalArgumentException if the origin is a {@link Origin#CONSTRAINT constraint},
	 * in which case {@link #Literal(Object,boolean,int)} should be used
	 */
	public Literal(Object var, boolean positive, Origin origin) throws IllegalArgumentException {
		this(var, positive);
		setOrigin(origin);
	}

	/**
	 * Creates a new literal.
	 * @param var contained variable
	 * @param positive whether the variable is positive or negated
	 * @param originConstraintIndex the index of the origin constraint in the feature model
	 */
	public Literal(Object var, boolean positive, int originConstraintIndex) {
		this(var, positive);
		setOriginConstraintIndex(originConstraintIndex);
	}

	/**
	 * Returns the origin of the literal.
	 * @return the origin of the literal
	 */
	public Origin getOrigin() {
		if (origin < 0) {
			return Origin.CONSTRAINT;
		}
		return Origin.values()[origin];
	}
	
	/**
	 * Sets the origin.
	 * @param origin origin of the literal
	 * @throws IllegalArgumentException if the origin is a {@link Origin#CONSTRAINT constraint},
	 * in which case {@link #setOriginConstraintIndex(int)} should be used
	 */
	public void setOrigin(Origin origin) throws IllegalArgumentException {
		if (origin == Origin.CONSTRAINT) {
			throw new IllegalArgumentException("Origin must not be a constraint");
		}
		this.origin = origin.ordinal();
	}

	/**
	 * Returns the origin constraint's index in the feature model.
	 * @return the origin constraint's index in the feature model
	 * @throws IllegalStateException if the origin is not a {@link Origin#CONSTRAINT constraint}
	 */
	public int getOriginConstraintIndex() throws IllegalStateException {
		if (getOrigin() != Origin.CONSTRAINT) {
			throw new IllegalStateException("Origin is not a constraint");
		}
		return ~origin;
	}

	/**
	 * Sets the origin by encoding the given origin constraint index.
	 * @param originConstraintIndex index of the origin constraint in the feature model
	 */
	public void setOriginConstraintIndex(int originConstraintIndex) {
		this.origin = ~originConstraintIndex;
	}

	public void flip() {
		positive = !positive;
	}

	@Override
	public boolean isConjunctiveNormalForm() {
		return true;
	}

	@Override
	public boolean isClausalNormalForm() {
		return false;
	}

	@Override
	protected Node eliminateNonCNFOperators(Node[] newChildren) {
		return clone();
	}

	@Override
	protected Node eliminate(List<Class<? extends Node>> list) {
		//nothing to do with children
		return this;
	}

	@Override
	protected Node clausify() {
		//nothing to do
		return this;
	}

	@Override
	public void simplify() {
		//nothing to do (recursive calls reached lowest node)
	}

	@Override
	protected List<Node> replaceFeature(IFeature feature, IFeature replaceWithFeature, List<Node> list) {
		if (this.var.equals(feature.getName())) {
			this.var = replaceWithFeature.getName();
			list.add(this);
		}
		return list;
	}

	@Override
	public Literal clone() {
		Literal copy = new Literal(var, positive);
		copy.origin = this.origin;
		return copy;
	}

	@Override
	public int hashCode() {
		return var.hashCode() * (positive ? 31 : 37);
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
		return (positive == other.positive) && (var.equals(other.var));
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		return this.positive == map.get(this.var);
	}
	
	@Override
	protected Collection<String> getContainedFeatures(Collection<String> containedFeatures) {
		containedFeatures.add(String.valueOf(this.var));
		return containedFeatures;
	}
	
	@Override
	protected Collection<Literal> getLiterals(Collection<Literal> literals) {
		literals.add(this);
		return literals;
	}
	
	@Override
	protected Collection<Object> getVariables(Collection<Object> variables) {
		variables.add(this.var);
		return variables;
	}
}