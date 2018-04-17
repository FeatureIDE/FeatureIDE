package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.composite;

import java.util.Collection;
import java.util.Deque;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.fm.impl.composite.CompositeFeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreator;

/**
 * Implements {@link PreprocessorExplanationCreator} through composition.
 *
 * @param <S> subject
 * @param <E> explanation
 * @author Timo G&uuml;nther
 */
public abstract class CompositePreprocessorExplanationCreator<S, E extends PreprocessorExplanation<S>, C extends PreprocessorExplanationCreator<S, E>>
		extends CompositeFeatureModelExplanationCreator<S, E, C> implements PreprocessorExplanationCreator<S, E> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param composites the explanation creators this composes
	 */
	protected CompositePreprocessorExplanationCreator(Collection<C> composites) {
		super(composites);
	}

	@Override
	public Deque<Node> getExpressionStack() {
		for (final C composite : getComposites()) {
			return composite.getExpressionStack();
		}
		return null;
	}

	@Override
	public void setExpressionStack(Collection<Node> expressionStack) {
		for (final C composite : getComposites()) {
			composite.setExpressionStack(expressionStack);
		}
	}
}
