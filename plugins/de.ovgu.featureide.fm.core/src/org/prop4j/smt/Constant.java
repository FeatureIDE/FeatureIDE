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
package org.prop4j.smt;

/**
 * Represents a constant type of the given generic {@link Datatype}
 *
 * @author Joshua Sprey
 */
public class Constant<T extends Datatype> extends Term {

	public T var;

	public Constant(T constant) {
		super(constant);
		this.var = constant;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#clone()
	 */
	@Override
	protected Constant<T> clone() {
		return new Constant<T>(var);
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.Term#getVar()
	 */
	@Override
	public T getValue() {
		return var;
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return getValue().toString();
	}

	/*
	 * (non-Javadoc)
	 * @see org.prop4j.Term#hashCode()
	 */
	@Override
	public int hashCode() {
		return super.hashCode() + (var.hashCode() * 5);
	}
}
