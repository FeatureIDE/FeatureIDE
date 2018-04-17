package de.ovgu.featureide.fm.core.explanations.config.impl.composite;

import java.util.Collection;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanation;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanationCreator;

/**
 * Implements {@link AutomaticSelectionExplanationCreator} through composition.
 *
 * @author Timo G&uuml;nther
 */
public class CompositeAutomaticSelectionExplanationCreator
		extends CompositeConfigurationExplanationCreator<SelectableFeature, AutomaticSelectionExplanation, AutomaticSelectionExplanationCreator>
		implements AutomaticSelectionExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param composites the explanation creators to compose
	 */
	public CompositeAutomaticSelectionExplanationCreator(Collection<AutomaticSelectionExplanationCreator> composites) {
		super(composites);
	}
}
