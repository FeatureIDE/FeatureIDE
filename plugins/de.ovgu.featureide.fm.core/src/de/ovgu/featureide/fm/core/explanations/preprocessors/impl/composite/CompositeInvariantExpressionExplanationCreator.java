package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.composite;

import java.util.Collection;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantExpressionExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantExpressionExplanationCreator;

/**
 * Implements {@link InvariantExpressionExplanationCreator} through composition.
 * 
 * @author Timo G&uuml;nther
 */
public class CompositeInvariantExpressionExplanationCreator extends CompositePreprocessorExplanationCreator<InvariantExpressionExplanationCreator>
		implements InvariantExpressionExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 * 
	 * @param composites the explanation creators to compose
	 */
	public CompositeInvariantExpressionExplanationCreator(Collection<InvariantExpressionExplanationCreator> composites) {
		super(composites);
	}

	@Override
	public Node getSubject() {
		return (Node) super.getSubject();
	}

	@Override
	public InvariantExpressionExplanation getExplanation() throws IllegalStateException {
		return (InvariantExpressionExplanation) super.getExplanation();
	}

	@Override
	public boolean isTautology() {
		for (final InvariantExpressionExplanationCreator composite : getComposites()) {
			return composite.isTautology();
		}
		return false;
	}

	@Override
	public void setTautology(boolean tautology) {
		for (final InvariantExpressionExplanationCreator composite : getComposites()) {
			composite.setTautology(tautology);
		}
	}
}
