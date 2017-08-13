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
package de.ovgu.featureide.fm.core.explanations.impl.mus;

import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.prop4j.Literal;
import org.prop4j.explain.solvers.MusExtractor;

import de.ovgu.featureide.fm.core.configuration.Configuration;
import de.ovgu.featureide.fm.core.configuration.SelectableFeature;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.AutomaticSelectionExplanationCreator;
import de.ovgu.featureide.fm.core.explanations.Explanation;

/**
 * Implementation of {@link AutomaticSelectionExplanationCreator} using a {@link MusExtractor MUS extractor}.
 * 
 * @author Timo G&uuml;nther
 */
public class MusAutomaticSelectionExplanationCreator extends MusConfigurationExplanationCreator implements AutomaticSelectionExplanationCreator {
	/**
	 * The features that have been added to the oracle.
	 * Stored for performance reasons.
	 */
	private final List<SelectableFeature> selectedFeatures = new LinkedList<>();
	
	/** The automatic selection to be explained. */
	private SelectableFeature automaticSelection;
	
	/**
	 * Constructs a new instance of this class.
	 */
	protected MusAutomaticSelectionExplanationCreator() {
		this(null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param config the configuration
	 */
	protected MusAutomaticSelectionExplanationCreator(Configuration config) {
		this(config, null);
	}
	
	/**
	 * Constructs a new instance of this class.
	 * @param fm the feature model context
	 * @param deadFeature the dead feature in the feature model
	 */
	protected MusAutomaticSelectionExplanationCreator(Configuration config, SelectableFeature automaticSelection) {
		super(config);
		setAutomaticSelection(automaticSelection);
	}
	
	@Override
	public SelectableFeature getAutomaticSelection() {
		return automaticSelection;
	}
	
	@Override
	public void setAutomaticSelection(SelectableFeature automaticSelection) {
		this.automaticSelection = automaticSelection;
	}
	
	@Override
	public Explanation getExplanation() throws IllegalStateException {
		final MusExtractor oracle = getOracle();
		final Explanation explanation;
		oracle.push();
		try {
			selectedFeatures.clear();
			for (final SelectableFeature featureSelection : getConfiguration().getFeatures()) {
				final Object var = featureSelection.getFeature().getName();
				final boolean value;
				if (featureSelection == getAutomaticSelection()) {
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
					oracle.addAssumption(var, value); //Assumptions do not show up in the explanation.
				} else {
					switch (featureSelection.getSelection()) {
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
		explanation.setAutomaticSelection(getAutomaticSelection());
		return explanation;
	}
	
	@Override
	protected Explanation getExplanation(Set<Integer> clauseIndexes) {
		final FeatureModelToNodeTraceModel traceModel = getTraceModel();
		final Explanation explanation = new Explanation();
		final int traceCount = traceModel.getTraceCount();
		for (final Integer clauseIndex : clauseIndexes) {
			if (clauseIndex >= traceCount) {
				explanation.addReason(selectedFeatures.get(clauseIndex - traceCount));
			} else {
				explanation.addReason(traceModel.getTrace(clauseIndex));
			}
		}
		return explanation;
	}
}