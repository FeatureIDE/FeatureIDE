/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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

/**
 * A variable or negated variable.
 * 
 * @author Thomas Thuem
 */
public class Literal extends Node {
	
	public Object var;
	
	public boolean positive;

	public Literal(Object var, boolean positive) {
		this.var = var;
		this.positive = positive;
	}
	
	public Literal(Object var) {
		this.var = var;
		positive = true;
	}

	public void flip() {
		positive = !positive;
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
		return new Literal(var, positive);
	}

	@Override
	public boolean equals(Object node) {
		if (!(node instanceof Literal))
			return false;
		return (var.equals(((Literal) node).var)) && (positive == ((Literal) node).positive);
	}
	
}
