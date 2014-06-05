package de.ovgu.featureide.ui.statistics.core.composite.lazyimplementations;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.sat4j.specs.TimeoutException;

import de.ovgu.featureide.fm.core.Feature;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.FeatureModelAnalyzer;
import de.ovgu.featureide.ui.statistics.core.composite.LazyParent;
import de.ovgu.featureide.ui.statistics.core.composite.Parent;

/**
 * Counts and categorizes features in the given feature model.
 * 
 * @author Dominik Hamann
 * @author Patrick Haese
 */
public final class StatisticsFeatureComplexity extends LazyParent {
	private FeatureModelAnalyzer ana;
	private FeatureModel model;

	
	public StatisticsFeatureComplexity(String description, FeatureModel model) {
		super(description, null);
		this.model = model;
		this.ana = model.getAnalyser();
	}

	@Override
	protected void initChildren() {
		if (model != null) {
			/*
			 * Calculates the actual statistics.
			 */
			final int constraints = model.getConstraintCount();

			Boolean isValid = null;
			try {
				isValid = ana.isValid();
			} catch (TimeoutException e) {
			}

			/*
			 * Creates a dataset.
			 */
			Collection<Feature> listOfFeatures = model.getFeatures();

			addChild(new Parent(MODEL_VOID, isValid == null ? MODEL_TIMEOUT
					: isValid));

			addChild(new FeatureListNode(NUMBER_FEATURES, listOfFeatures));

			addChild(new FeatureListNode(NUMBER_CONCRETE,
					model.getConcreteFeatures()));

			List<Feature> listOfAbstractFeatures = new LinkedList<Feature>();
			for (Feature f : listOfFeatures) {
				if (f.isAbstract()) {
					listOfAbstractFeatures.add(f);
				}
			}
			addChild(new FeatureListNode(NUMBER_ABSTRACT,
					listOfAbstractFeatures));

			List<Feature> listOfCompoundFeatures = new LinkedList<Feature>();
			for (Feature f : listOfFeatures) {
				if (!f.getChildren().isEmpty()) {
					listOfCompoundFeatures.add(f);
				}
			}
			addChild(new FeatureListNode(NUMBER_COMPOUND,
					listOfCompoundFeatures));

			List<Feature> listOfPrimitiveFeatures = new LinkedList<Feature>();
			for (Feature f : listOfFeatures) {
				if (f.getChildren().isEmpty()) {
					listOfPrimitiveFeatures.add(f);
				}
			}
			addChild(new FeatureListNode(NUMBER_TERMINAL,
					listOfPrimitiveFeatures));

			addChild(new FeatureListNode(NUMBER_HIDDEN, ana.getHiddenFeatures()));
			
			addChild(new Parent(NUMBER_CONSTRAINTS, constraints));

		}
	}
}