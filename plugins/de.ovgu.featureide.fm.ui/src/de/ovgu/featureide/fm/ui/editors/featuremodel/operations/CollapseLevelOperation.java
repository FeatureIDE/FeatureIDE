package de.ovgu.featureide.fm.ui.editors.featuremodel.operations;

import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW_SUBTREE;

import java.util.LinkedList;
import java.util.List;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Operation that expands all features up to a certain level starting from a selected feature. The features at that level are collapsed. Enables undo/redo
 * functionality.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class CollapseLevelOperation extends AbstractGraphicalFeatureModelOperation {

	private final String featureName;
	private final int level;

	private final List<IGraphicalFeature> collapsedGraphicalFeatures;

	public CollapseLevelOperation(String featureName, IGraphicalFeatureModel graphicalFeatureModel, int level) {
		super(graphicalFeatureModel, SHOW_SUBTREE);
		this.featureName = featureName;
		this.level = level;

		collapsedGraphicalFeatures = new LinkedList<>();
	}

	@Override
	protected FeatureIDEEvent operation(IFeatureModel featureModel) {
		collapsedGraphicalFeatures.clear();
		final IFeature feature = featureModel.getFeature(featureName);

		collapseToLevel(feature, 0);

		return new FeatureIDEEvent(feature, FeatureIDEEvent.EventType.FEATURE_COLLAPSED_CHANGED);
	}

	/**
	 * Recursively expand all features until the desired level. The features at that level are collapsed. All features that were collapsed before are saved.
	 *
	 * @param currentFeature The current feature being looked at
	 * @param currentLevel The current level
	 */
	private void collapseToLevel(IFeature currentFeature, int currentLevel) {
		final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(currentFeature);

		// save features that were collapsed before the operation
		if (graphicalFeature.isCollapsed()) {
			collapsedGraphicalFeatures.add(graphicalFeature);
		}

		if (currentLevel == level) {
			graphicalFeature.setCollapsed(true);
		} else {
			graphicalFeature.setCollapsed(false);
			for (final IFeatureStructure featureStructure : currentFeature.getStructure().getChildren()) {
				collapseToLevel(featureStructure.getFeature(), currentLevel + 1);
			}
		}
	}

	@Override
	protected FeatureIDEEvent inverseOperation(IFeatureModel featureModel) {
		final IFeature feature = featureModel.getFeature(featureName);

		expandToLevel(feature, 0);

		// restore all features that were collapsed before the operation
		for (final IGraphicalFeature graphicalFeature : collapsedGraphicalFeatures) {
			graphicalFeature.setCollapsed(true);
		}

		return new FeatureIDEEvent(feature, FeatureIDEEvent.EventType.FEATURE_COLLAPSED_CHANGED);
	}

	/**
	 * Recursively expand all features until the desired level. The features at that level are also expanded.
	 *
	 * @param currentFeature The current feature being looked at
	 * @param currentLevel The current level
	 */
	private void expandToLevel(IFeature currentFeature, int currentLevel) {
		final IGraphicalFeature graphicalFeature = graphicalFeatureModel.getGraphicalFeature(currentFeature);

		graphicalFeature.setCollapsed(false);
		if (currentLevel < level) {
			for (final IFeatureStructure featureStructure : currentFeature.getStructure().getChildren()) {
				expandToLevel(featureStructure.getFeature(), currentLevel + 1);
			}
		}
	}
}
