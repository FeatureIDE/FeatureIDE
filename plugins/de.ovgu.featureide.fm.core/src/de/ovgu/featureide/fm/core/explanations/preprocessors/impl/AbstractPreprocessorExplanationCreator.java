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
package de.ovgu.featureide.fm.core.explanations.preprocessors.impl;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.fm.impl.AbstractFeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreator;

/**
 * Abstract implementation of {@link PreprocessorExplanationCreator}.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <O> oracle
 * @author Timo G&uuml;nther
 */
public abstract class AbstractPreprocessorExplanationCreator<S, E extends PreprocessorExplanation<S>, O> extends AbstractFeatureModelExplanationCreator<S, E, O>
		implements PreprocessorExplanationCreator<S, E> {

	/** The expression stack. */
	private Deque<Node> expressionStack;

	@Override
	public Deque<Node> getExpressionStack() {
		return expressionStack;
	}

	@Override
	public void setExpressionStack(Collection<Node> expressionStack) {
		this.expressionStack = new ArrayDeque<>(expressionStack);
	}
}
