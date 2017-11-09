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
package de.ovgu.featureide.fm.core.explanations.impl.composite;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.impl.ltms.Ltms;

import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.ExplanationCreator;

/**
 * Implements {@link ExplanationCreator} by composing any number of other instances. Delegates to these other composite instances to do the actual work. Useful
 * if some instances fail to consistently generate explanations but are otherwise preferable. For example, {@link Ltms LTMS} is fast but incomplete. If it
 * fails, one might try again with a slower but complete {@link MusExtractor MUS extractor}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <C> composite
 * @author Timo G&uuml;nther
 */
public abstract class CompositeExplanationCreator<S, E extends Explanation<S>, C extends ExplanationCreator<S, E>> implements ExplanationCreator<S, E> {

	/** The explanation creators this composes. */
	private final List<C> composites;

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param composites the explanation creators to compose
	 */
	public CompositeExplanationCreator(Collection<C> composites) {
		this.composites = new ArrayList<>(composites);
	}

	/**
	 * Returns the explanation creators this composes.
	 *
	 * @return the explanation creators this composes
	 */
	public List<C> getComposites() {
		return composites;
	}

	@Override
	public S getSubject() {
		for (final C composite : getComposites()) {
			return composite.getSubject();
		}
		return null;
	}

	@Override
	public void setSubject(S subject) {
		for (final C composite : getComposites()) {
			composite.setSubject(subject);
		}
	}

	@Override
	public E getExplanation() throws IllegalStateException {
		for (final C composite : getComposites()) {
			final E explanation = composite.getExplanation();
			if (explanation != null) {
				return explanation;
			}
		}
		return null;
	}
}
