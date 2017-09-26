package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.composite;

import java.util.Collection;
import java.util.Deque;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.fm.impl.composite.CompositeFeatureModelExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.preprocessors.PreprocessorExplanationCreator;

/**
 * Implements {@link PreprocessorExplanationCreator} through composition.
 * 
 * @author Timo G&uuml;nther
 */
public abstract class CompositePreprocessorExplanationCreator<T extends PreprocessorExplanationCreator> extends CompositeFeatureModelExplanationCreator<T>
		implements PreprocessorExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 * 
	 * @param composites the explanation creators this composes
	 */
	public CompositePreprocessorExplanationCreator(Collection<T> composites) {
		super(composites);
	}

	@Override
	public Deque<Node> getExpressionStack() {
		for (final T composite : getComposites()) {
			return composite.getExpressionStack();
		}
		return null;
	}

	@Override
	public void setExpressionStack(Collection<Node> expressionStack) {
		for (final T composite : getComposites()) {
			composite.setExpressionStack(expressionStack);
		}
	}
}
