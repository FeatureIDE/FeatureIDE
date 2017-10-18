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
package de.ovgu.featureide.core.signature.base;

import java.util.List;

public abstract class AbstractMethodSignature extends AbstractSignature {

	protected List<String> parameterTypes;
	protected final boolean isConstructor;

	protected AbstractMethodSignature(AbstractClassSignature parent, String name, String modifier, String type, List<String> parameterTypes,
			boolean isConstructor) {
		super(parent, name, modifier, type);
		this.isConstructor = isConstructor;
		this.parameterTypes = parameterTypes;
	}

	protected AbstractMethodSignature(AbstractClassSignature parent, String name, String modifier, String type, List<String> parameterTypes,
			boolean isConstructor, int startLine, int endLine) {
		super(parent, name, modifier, type, startLine, endLine);
		this.isConstructor = isConstructor;
		this.parameterTypes = parameterTypes;
	}

	public abstract String getReturnType();

	public List<String> getParameterTypes() {
		return parameterTypes;
	}

	public boolean isConstructor() {
		return isConstructor;
	}

}
