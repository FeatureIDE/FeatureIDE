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
package de.ovgu.featureide.fm.core.explanations.config.impl.mus;

import org.prop4j.Node;
import org.prop4j.explain.solvers.MusExtractor;
import org.prop4j.explain.solvers.SatSolverFactory;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.config.impl.AbstractConfigurationExplanationCreator;

/**
 * Abstract implementation of {@link ConfigurationExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public abstract class MusConfigurationExplanationCreator extends AbstractConfigurationExplanationCreator {

	/**
	 * The oracle with the CNF as input. The oracle is created lazily when needed and reset when the CNF changes.
	 */
	private MusExtractor oracle;

	/**
	 * Constructs a new instance of this class.
	 */
	protected MusConfigurationExplanationCreator() {
		this(null);
	}

	/**
	 * Constructs a new instance of this class.
	 *
	 * @param config the configuration
	 */
	protected MusConfigurationExplanationCreator(Configuration config) {
		setConfiguration(config);
	}

	/**
	 * Returns the oracle. Creates it first if necessary.
	 *
	 * @return the oracle; not null
	 */
	protected MusExtractor getOracle() {
		if (oracle == null) {
			setOracle();
		}
		return oracle;
	}

	/**
	 * Sets the oracle.
	 */
	protected void setOracle() {
		final Node cnf = getCnf();
		if (cnf == null) {
			oracle = null;
			return;
		}
		final MusExtractor oracle = SatSolverFactory.getDefault().getMusExtractor();
		oracle.addFormula(cnf);
		this.oracle = oracle;
	}

	@Override
	protected Node setCnf() {
		final Node cnf = super.setCnf();
		if (cnf != null) {
			setOracle();
		}
		return cnf;
	}
}
