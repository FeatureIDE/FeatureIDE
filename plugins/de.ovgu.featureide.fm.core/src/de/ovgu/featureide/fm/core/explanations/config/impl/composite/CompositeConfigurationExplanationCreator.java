/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
