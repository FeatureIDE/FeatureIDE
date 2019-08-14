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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.core.configuration;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.analysis.cnf.formula.FeatureModelFormula;
import de.ovgu.featureide.fm.core.job.LongRunningWrapper;

/**
 * Analyzes a configuration.
 *
 * @author Sebastian Krieter
 */
public class ConfigurationAnalyzer {

	private final IConfigurationPropagator propagator;

	public ConfigurationAnalyzer(IConfigurationPropagator propagator) {
		this.propagator = propagator;
	}

	public ConfigurationAnalyzer(FeatureModelFormula formula, Configuration configuration) {
		propagator = new ConfigurationPropagator(formula, configuration);
		propagator.setIncludeAbstractFeatures(true);
	}

	public boolean isIncludeAbstractFeatures() {
		return propagator.isIncludeAbstractFeatures();
	}

	public void setIncludeAbstractFeatures(boolean includeAbstractFeatures) {
		propagator.setIncludeAbstractFeatures(includeAbstractFeatures);
	}

	public boolean canBeValid() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.canBeValid());
		return (result != null) ? result : false;
	}

	public void resolve() {
		LongRunningWrapper.runMethod(propagator.resolve());
	}

	/**
	 * Creates solutions to cover the given features.
	 *
	 * @param features The features that should be covered.
	 * @param selection true is the features should be selected, false otherwise.
	 * @return a list of configurations (list of selected feature names)
	 */
	public List<List<String>> coverFeatures(final Collection<String> features, final boolean selection) {
		final List<List<String>> result = LongRunningWrapper.runMethod(propagator.coverFeatures(features, selection));
		return result != null ? result : Collections.emptyList();
	}

	public Collection<SelectableFeature> findOpenClauses() {
		final Collection<SelectableFeature> result = LongRunningWrapper.runMethod(propagator.findOpenClauses());
		return result != null ? result : Collections.emptyList();
	}

	public List<List<String>> getSolutions(int max) throws TimeoutException {
		final List<List<String>> result = LongRunningWrapper.runMethod(propagator.getSolutions(max));
		return result != null ? result : Collections.emptyList();
	}

	public boolean isValid() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.isValid());
		return (result != null) ? result : false;
	}

	/**
	 * Ignores hidden features. Use this, when propagate is disabled (hidden features are not updated).
	 * 
	 * @return true, if configuration is valid
	 */
	public boolean isValidNoHidden() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.isValidNoHidden());
		return (result != null) ? result : false;
	}

	/**
	 * Counts the number of possible solutions.
	 *
	 * @param timeout The timeout in milliseconds.
	 * @return A positive value equal to the number of solutions (if the method terminated in time)<br> or a negative value (if a timeout occurred) that
	 *         indicates that there are more solutions than the absolute value
	 */
	public long number(int timeout) {
		final Long result = LongRunningWrapper.runMethod(propagator.number(timeout));
		return (result != null) ? result : 0;
	}

	public long number() {
		final Long result = LongRunningWrapper.runMethod(propagator.number(1000));
		return (result != null) ? result : 0;
	}

	public Collection<SelectableFeature> update(boolean redundantManual, List<SelectableFeature> featureOrder) {
		final Collection<SelectableFeature> result = LongRunningWrapper.runMethod(propagator.update(redundantManual, featureOrder));
		return (result != null) ? result : Collections.emptyList();
	}

	public Collection<SelectableFeature> update(boolean redundantManual) {
		final Collection<SelectableFeature> result = LongRunningWrapper.runMethod(propagator.update(redundantManual));
		return (result != null) ? result : Collections.emptyList();
	}

	public Collection<SelectableFeature> update() {
		final Collection<SelectableFeature> result = LongRunningWrapper.runMethod(propagator.update());
		return (result != null) ? result : Collections.emptyList();
	}

	public boolean completeRandomly() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.completeRandomly());
		return (result != null) ? result : false;
	}

	public boolean completeMin() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.completeMin());
		return (result != null) ? result : false;
	}

	public boolean completeMax() {
		final Boolean result = LongRunningWrapper.runMethod(propagator.completeMax());
		return (result != null) ? result : false;
	}

}
