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
package org.prop4j;

import java.security.InvalidParameterException;
import java.util.List;
import java.util.Map;

/**
 * A variable or negated variable.
 * 
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public class Literal extends Node implements Cloneable {

	public Object var;

	public boolean positive;

	//annotate each literal of a formula with an attribute for explanation. If "Up", explain child relationship
	// to parent from feature-tree. If "Constraint", explain using cross-tree constraint.
	public enum FeatureAttribute {
		UNDEFINED,
		CHILD,
		PARENT,
		ROOT,
		CONSTRAINT
	};

	public int origin; // attribute encodes relevant information for generating explanations


	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}

	public Literal(Object var) {
		this.var = var;
		positive = true;
	}
	
	/**
	 * Encodes a literal from the tree topology.
	 * FeatureAttribute must not have the value Constraint.
	 * Example with root as FeatureAttribute: origin = -1 * 5 + 3 = -2 
	 * @param var The variable 
	 * @param FeatureAttribute The Enumeration element  
	 */
	public Literal(Object var, FeatureAttribute a) {
		this(var);
		if (a == FeatureAttribute.CONSTRAINT) {
			throw new InvalidParameterException("Parameter Constraint is not allowed");
		}
		this.origin = -1 * FeatureAttribute.values().length + a.ordinal();  
	}																	   

	/**
	 * Encodes a literal from a constraint.
	 * @param var The variable
	 * @param constraintIndex The index of a constraint  
	 */
	public Literal(Object var, int constraintIndex) {
		this(var);
		setOriginConstraint(constraintIndex);  
	}										  

	/**
	 * Decodes a constraint index.    
	 * Example with origin = 4: origin = 4 / 5 = 0. Returns a constraint with index 0.
	 * 
	 * @return The constraint-index
	 */
	public int getSourceIndex() {
		if (getSourceAttribute() != FeatureAttribute.CONSTRAINT) {
			throw new IllegalStateException("origin is not Constraint");
		}
		return origin / FeatureAttribute.values().length;
	}

	/**
	 * Decodes a FeatureAttribute. 
	 * Example with FeatureAttribute root and origin of -2: -2 % 5 + 5 = 3. 
	 * Returns a FeatureAttribute with value 3 (ordinal).   
	 * 
	 * @return FeatureAttribute The Enumeration element  
	 */
	public FeatureAttribute getSourceAttribute() {
		int index = origin % FeatureAttribute.values().length;
		if (index < 0) {
			index += FeatureAttribute.values().length;
		}
		return FeatureAttribute.values()[index];
	}

	/**
	 * Encodes a constraint-index.  
	 * Example with constraintIndex = 0: origin = 0 * 5 + 4 = 4
	 * @param constrIndex The index of a constraint
	 */
	public void setOriginConstraint(int constrIndex) {
		this.origin = constrIndex * FeatureAttribute.values().length + FeatureAttribute.CONSTRAINT.ordinal();
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

}