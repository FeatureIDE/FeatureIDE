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
package de.ovgu.featureide.fm.core.explanations.preprocessors;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.Reason;

/**
 * A reason of an explanation involving a preprocessor.
 *
 * @author Timo G&uuml;nther
 */
public class PreprocessorReason extends Reason {

	/** An expression from the expression stack. */
	private final Node expression;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param expression an expression from the expression stack; not null
	 */
	public PreprocessorReason(Node expression) {
		this.expression = expression;
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param reason the reason to clone; not null
	 */
	protected PreprocessorReason(PreprocessorReason reason) {
		super(reason);
		expression = reason.expression;
	}

	/**
	 * Returns the expression of this reason.
	 *
	 * @return the expression of this reason; not null
	 */
	public Node getExpression() {
		return expression;
	}

	@Override
	protected PreprocessorReason clone() {
		return new PreprocessorReason(expression);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = (prime * result) + ((expression == null) ? 0 : expression.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final PreprocessorReason other = (PreprocessorReason) obj;
		if (expression == null) {
			if (other.expression != null) {
				return false;
			}
		} else if (!expression.equals(other.expression)) {
			return false;
		}
		return true;
	}
}
