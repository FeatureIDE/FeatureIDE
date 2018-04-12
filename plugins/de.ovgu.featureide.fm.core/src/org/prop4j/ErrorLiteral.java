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

import java.util.Map;

/**
 * Holds an unparsable sub expression from a formula that could not be parsed completely by the {@link NodeReader}.
 *
 * @author Sebastian Krieter
 */
public class ErrorLiteral extends Literal {

	public ErrorLiteral(Object var) {
		super(var, true);
	}

	public ErrorLiteral(ErrorLiteral oldLiteral) {
		super(oldLiteral);
	}

	@Override
	public ErrorLiteral clone() {
		return new ErrorLiteral(this);
	}

	@Override
	public boolean getValue(Map<Object, Boolean> map) {
		return false;
	}

}
