package de.ovgu.featureide.fm.core.explanations.config.impl.composite;

import java.util.Collection;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.fm.impl.composite.CompositeFeatureModelExplanationCreator;

/**
 * Implements {@link ConfigurationExplanationCreator} through composition.
 * 
 * @author Timo G&uuml;nther
 */
public abstract class CompositeConfigurationExplanationCreator<T extends ConfigurationExplanationCreator> extends CompositeFeatureModelExplanationCreator<T>
		implements ConfigurationExplanationCreator {

	/**
	 * Constructs a new instance of this class.
	 * 
	 * @param composites the explanation creators this composes
	 */
	public CompositeConfigurationExplanationCreator(Collection<T> composites) {
		super(composites);
	}

	@Override
	public Configuration getConfiguration() {
		for (final T composite : getComposites()) {
			return composite.getConfiguration();
		}
		return null;
	}

	@Override
	public void setConfiguration(Configuration config) {
		for (final T composite : getComposites()) {
			composite.setConfiguration(config);
		}
	}
}
