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
package de.ovgu.featureide.fm.core.explanations;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;
import org.prop4j.And;
import org.prop4j.Node;
import org.prop4j.Not;
import org.prop4j.SatSolver;
import org.sat4j.specs.TimeoutException;

/**
 * Tests for {@link ExplanationCreator}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <C> explanation creator
 * @author Timo G&uuml;nther
 */
public abstract class ExplanationCreatorTests<S, E extends Explanation<S>, C extends ExplanationCreator<S, E>> {

	@Rule
	public final ExpectedException exception = ExpectedException.none();

	@Test
	public void testSubjectNull() {
		final C c = getInstance();
		c.setSubject(null);
		exception.expect(IllegalStateException.class);
		c.getExplanation();
	}

	/**
	 * Checks whether the given explanation is valid. That is the case if the formula it represents is unsatisfiable.
	 *
	 * @param explanation the explanation to check
	 * @return true iff the given explanation is valid
	 */
	protected boolean isValid(E explanation) {
		final Node node = new And(explanation.toNode(), new Not(explanation.getImplication()));
		try {
			return !new SatSolver(node, 1000).isSatisfiable();
		} catch (final TimeoutException e) {
			throw new RuntimeException(e);
		}
	}

	/**
	 * Returns an instance to test.
	 *
	 * @return an instance to test
	 */
	protected abstract C getInstance();
}
