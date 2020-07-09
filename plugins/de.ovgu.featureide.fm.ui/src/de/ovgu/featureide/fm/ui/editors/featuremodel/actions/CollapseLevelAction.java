package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.LEVEL;
import static de.ovgu.featureide.fm.core.localization.StringTable.LEVELS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SHOW;

import org.eclipse.jface.resource.ImageDescriptor;

import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.CollapseLevelOperation;
import de.ovgu.featureide.fm.ui.editors.featuremodel.operations.FeatureModelOperationWrapper;

/**
 * Action to show the subtree up to a certain level. See {@link CollapseLevelOperation}.
 *
 * @author Philipp Vulpius
 * @author Soeren Viegener
 */
public class CollapseLevelAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.collapselevel";
	private final ImageDescriptor imageDescriptor = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif");

	private final IGraphicalFeatureModel graphicalFeatureModel;
	private final int level;

	/**
	 * @param viewer viewer that calls this action
	 * @param graphicalFeatureModel graphical feature model
	 * @param level level to which the subtree is shown, starting with the selected feature.
	 */
	public CollapseLevelAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel, int level) {
		// label: "Show 3 Levels" or "Show 1 Level"
		super(SHOW + " " + level + " " + ((level == 1) ? LEVEL : LEVELS), viewer, ID, graphicalFeatureModel.getFeatureModelManager());
		setImageDescriptor(imageDescriptor);
		this.graphicalFeatureModel = graphicalFeatureModel;
		this.level = level;
	}

	@Override
	public void run() {
		FeatureModelOperationWrapper.run(new CollapseLevelOperation(getSelectedFeature().getName(), graphicalFeatureModel, level));
	}

	@Override
	protected void updateProperties() {}
}
