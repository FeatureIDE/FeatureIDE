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
		Undef, Up, Down, Root, Constraint
	};

	public int origin; // combined member of sourceIndex for cross-tree constraint and of enum type, used for explanations

	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}

	public Literal(Object var) {
		this.var = var;
		positive = true;
	}

	public Literal(Object var, FeatureAttribute a) {
		this(var);
		this.origin = -1 * FeatureAttribute.values().length + a.ordinal(); // encodes an enumeration type with an int member for explanations  
	}																	   // example with root as feature attribute: origin = -1 * 5 + 3 = -2 

	public Literal(Object var, int constraintIndex) {
		this(var);
		setOriginConstraint(constraintIndex); //encodes a constraint index with the same int member as for an enumeration type 
	}										  

	/**
	 * Decodes a constraint index.    
	 * Example with origin = 4: origin = 4 / 5 = 0. Returns a constraint with index 0.
	 * 
	 * @return the index of a constraint
	 */
	public int getSourceIndex() {
		return origin / FeatureAttribute.values().length;
	}

	/**
	 * Decodes a feature attribute from the feature tree topology. 
	 * Example with feature attribute root and origin = -2: -2 % 5 + 5 = 3. Returns a feature attribute at position 3.   
	 * 
	 * @return an enumeration type of a feature attribute
	 */
	public FeatureAttribute getSourceAttribute() {
		int index = origin % FeatureAttribute.values().length;
		if (index < 0) {
			index += FeatureAttribute.values().length; // add number of enum types to get positive index
		}
		return FeatureAttribute.values()[index];
	}

	/**
	 * Encodes a constraint index with an combined integer for explaining feature attributes and cross-tree constraints.  
	 * Example with constraintIndex = 0: origin = 0 * 5 + 4 = 4
	 * @param constrIndex
	 */
	public void setOriginConstraint(int constrIndex) {
		this.origin = constrIndex * FeatureAttribute.values().length + FeatureAttribute.Constraint.ordinal();
	}

	public void flip() {
		positive = !positive;
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

	/*	@Override
		public Literal clone() { 
			Literal copy = new Literal (var,positive);
			copy.setSourceIndex(this.srcIndex);
			copy.setFeatureAttribute(this.srcAttribute);
			return copy;
		}*/

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