package de.ovgu.featureide.fm.core.explanations.config.impl.composite;

import java.util.Collection;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanation;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.impl.composite.CompositeFeatureModelExplanationCreator;

/**
 * Implements {@link ConfigurationExplanationCreator} through composition.
 *
 * @param <S> subject
 * @param <E> explanation
 * @param <C> composite
 * @author Timo G&uuml;nther
 */
public abstract class CompositeConfigurationExplanationCreator<S, E extends ConfigurationExplanation<S>, C extends ConfigurationExplanationCreator<S, E>>
		extends CompositeFeatureModelExplanationCreator<S, E, C> implements ConfigurationExplanationCreator<S, E> {

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param composites the explanation creators this composes
	 */
	public CompositeConfigurationExplanationCreator(Collection<C> composites) {
		super(composites);
	}

	@Override
	public Configuration getConfiguration() {
		for (final C composite : getComposites()) {
			return composite.getConfiguration();
		}
		return null;
	}

	@Override
	public void setConfiguration(Configuration config) {
		for (final C composite : getComposites()) {
			composite.setConfiguration(config);
		}
	}
}
