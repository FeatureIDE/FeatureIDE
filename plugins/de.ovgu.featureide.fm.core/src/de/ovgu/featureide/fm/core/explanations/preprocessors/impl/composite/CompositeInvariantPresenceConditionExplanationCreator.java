package de.ovgu.featureide.fm.core.explanations.preprocessors.impl.composite;

import java.util.Collection;

import org.prop4j.Node;

import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanation;
import de.ovgu.featureide.fm.core.explanations.preprocessors.InvariantPresenceConditionExplanationCreator;

/**
 * Implements {@link InvariantPresenceConditionExplanationCreator} through composition.
 *
 * @author Timo G&uuml;nther
 */
public class CompositeInvariantPresenceConditionExplanationCreator
		extends CompositePreprocessorExplanationCreator<Node, InvariantPresenceConditionExplanation, InvariantPresenceConditionExplanationCreator>
		implements InvariantPresenceConditionExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param composites the explanation creators to compose
	 */
	protected CompositeInvariantPresenceConditionExplanationCreator(Collection<InvariantPresenceConditionExplanationCreator> composites) {
		super(composites);
	}

	@Override
	public InvariantPresenceConditionExplanation getExplanation() throws IllegalStateException {
		return (InvariantPresenceConditionExplanation) super.getExplanation();
	}

	@Override
	public boolean isTautology() {
		for (final InvariantPresenceConditionExplanationCreator composite : getComposites()) {
			return composite.isTautology();
		}
		return false;
	}

	@Override
	public void setTautology(boolean tautology) {
		for (final InvariantPresenceConditionExplanationCreator composite : getComposites()) {
			composite.setTautology(tautology);
		}
	}
}
