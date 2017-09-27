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

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.editing.NodeCreator;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanation;
import de.ovgu.featureide.fm.core.explanations.config.AutomaticSelectionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.config.ConfigurationReason;

/**
 * Implementation of {@link AutomaticSelectionExplanationCreator} using a {@link MusExtractor MUS extractor}.
 *
 * @author Timo G&uuml;nther
 */
public class MusAutomaticSelectionExplanationCreator extends MusConfigurationExplanationCreator implements AutomaticSelectionExplanationCreator {

	/**
	 * The features that have been added to the oracle. Stored for performance reasons.
	 */
	private final List<SelectableFeature> selectedFeatures = new LinkedList<>();

	@Override
	public SelectableFeature getSubject() {
		return (SelectableFeature) super.getSubject();
	}

	@Override
	public void setSubject(Object subject) throws IllegalArgumentException {
		if ((subject != null) && !(subject instanceof SelectableFeature)) {
			throw new IllegalArgumentException("Illegal subject type");
		}
		super.setSubject(subject);
	}

	@Override
	public AutomaticSelectionExplanation getExplanation() throws IllegalStateException {
		final MusExtractor oracle = getOracle();
		final AutomaticSelectionExplanation explanation;
		oracle.push();
		try {
			selectedFeatures.clear();
			for (final SelectableFeature featureSelection : getConfiguration().getFeatures()) {
				final Object var = NodeCreator.getVariable(featureSelection.getFeature());
				final boolean value;
				if (featureSelection == getSubject()) {
					switch (featureSelection.getAutomatic()) {
					case SELECTED:
						value = false;
						break;
					case UNSELECTED:
						value = true;
						break;
					case UNDEFINED:
						throw new IllegalStateException("Feature not automatically selected or unselected");
					default:
						throw new IllegalStateException("Unknown feature selection state");
					}
					oracle.addAssumption(var, value); // Assumptions do not show up in the explanation.
				} else {
					switch (featureSelection.getManual()) {
					case SELECTED:
						value = true;
						break;
					case UNSELECTED:
						value = false;
						break;
					case UNDEFINED:
						continue;
					default:
						throw new IllegalStateException("Unknown feature selection state");
					}
					oracle.addFormula(new Literal(var, value));
					selectedFeatures.add(featureSelection);
				}
			}
			explanation = getExplanation(oracle.getMinimalUnsatisfiableSubsetIndexes());
		} finally {
			oracle.pop();
		}
		return explanation;
	}

	@Override
	protected AutomaticSelectionExplanation getExplanation(Set<Integer> clauseIndexes) {
		return (AutomaticSelectionExplanation) super.getExplanation(clauseIndexes);
	}

	@Override
	protected Reason getReason(int clauseIndex) {
		final int selectionIndex = clauseIndex - getTraceModel().getTraceCount();
		if (selectionIndex >= 0) {
			return new ConfigurationReason(selectedFeatures.get(selectionIndex));
		}
		return super.getReason(clauseIndex);
	}

	@Override
	protected AutomaticSelectionExplanation getConcreteExplanation() {
		return new AutomaticSelectionExplanation(getSubject(), getConfiguration());
	}
}
