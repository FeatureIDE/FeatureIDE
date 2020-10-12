package de.ovgu.featureide.fm.ui.views.constraintview.content;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.PatternSyntaxException;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeatureModelElement;
import de.ovgu.featureide.fm.core.editing.FeatureModelToNodeTraceModel;
import de.ovgu.featureide.fm.core.explanations.Explanation;
import de.ovgu.featureide.fm.core.explanations.Reason;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeature;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.FeatureEditPart;

/**
 * This class filters the Constraints that should be shown in the ConstraintView according to whichever selections are made in the diagram and the search bar.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewFilter extends ViewerFilter {

	private List<FeatureEditPart> selection;
	private final List<IConstraint> explanationConstraints = new ArrayList<>();
	private String searchText = "";
	private IGraphicalFeatureModel graphicalFeatureModel;

	private final boolean caseSensitive = false;

	/**
	 * Sets the GraphicalFeatureModel to be used for filtering collapsed constraints
	 *
	 * @param graphicalFeatureModel The GraphicalFeatureModel to be used for filtering
	 */
	public void setGraphicalFeatureModel(IGraphicalFeatureModel graphicalFeatureModel) {
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	/**
	 * This method gets called whenever an Explanation in the FeatureModel is changed and updates the List of Explanations for the Constraints.
	 *
	 * @param activeExplanation the current active Explanation of the FeatureModel
	 */
	public void setActiveExplanation(Explanation<?> activeExplanation) {
		explanationConstraints.clear();

		if (activeExplanation == null) {
			return;
		}

		for (final Reason<?> r : activeExplanation.getReasons()) {
			if (r.getSubject() instanceof FeatureModelToNodeTraceModel.FeatureModelElementTrace) {
				final IFeatureModelElement element = ((FeatureModelToNodeTraceModel.FeatureModelElementTrace) r.getSubject()).getElement();
				if (element instanceof IConstraint) {
					explanationConstraints.add((IConstraint) element);
				}
			}
		}
	}

	public void setFeatureModelSelection(List<FeatureEditPart> selection) {
		this.selection = selection;
	}

	public List<FeatureEditPart> getFeatureModelSelection() {
		return selection;
	}

	public void setSearchText(String searchText) {
		this.searchText = searchText;
	}

	/**
	 * This method decides which Constraints should be displayed in the TreeViewer of the ConstraintView according to which parts are selected and the string in
	 * the search bar.
	 *
	 * @param viewer the TreeViewer of the ConstraintView
	 * @param parentElement only needed for Tree operations. Not needed in our case. (as we basically use a TreeViewer as a TableViewer)
	 * @param element the current Constraint which is checked whether it should be displayed or not
	 *
	 * @return true, if a Constraint should be displayed, i.e. is selected, searched for, or nothing is selected/searched for -> Then all Constraints should be
	 *         displayed.
	 */
	@Override
	public boolean select(Viewer viewer, Object parentElement, Object element) {
		// special case if no FeatureModel is open the String "open a Feature Diagram" will be given, which should be displayed
		if (element instanceof String) {
			return true;
		}
		final IConstraint constraint = (IConstraint) element;

		// filter by collapsed features
		if ((graphicalFeatureModel != null) && !graphicalFeatureModel.getLayout().showCollapsedConstraints()) {
			if (graphicalFeatureModel.getGraphicalConstraint(constraint).isCollapsed()) {
				return false;
			}
		}

		// filter by selection and explanation
		if ((selection != null) && !selection.isEmpty()) {

			if (!constraintInSelection(constraint) && !constraintInExplanation(constraint)) {
				return false;
			}
		}

		// filter by search text
		if ((searchText != null) && !searchText.isEmpty()) {
			if (!constraintInSearch(constraint)) {
				return false;
			}
		}

		return true;
	}

	private boolean constraintInExplanation(IConstraint constraint) {
		return explanationConstraints.contains(constraint);
	}

	/**
	 * Returns true if a given Constraint matches the current String in the search bar of the Constraint View.
	 *
	 * @param constraint which is checked
	 * @return true if the given Constraint matches. False otherwise.
	 */
	private boolean constraintInSearch(IConstraint constraint) {
		String currentSearchText = searchText;
		String constraintText = constraint.getDisplayName();
		String constraintDescription = constraint.getDescription();

		constraintDescription = constraintDescription.replaceAll("\n", " ");
		constraintDescription = constraintDescription.replaceAll("\r", " ");

		if (!caseSensitive) {
			constraintText = constraintText.toLowerCase();
			constraintDescription = constraintDescription.toLowerCase();
			currentSearchText = currentSearchText.toLowerCase();
		}

		final String regexSearch = ".*" + currentSearchText + ".*";

		// to avoid problems when invalid regex searches are entered
		try {
			return (constraintText.matches(regexSearch) || constraintDescription.matches(regexSearch));
		} catch (final PatternSyntaxException e) {
			return (constraintText.contains(currentSearchText) || constraintDescription.contains(currentSearchText));
		}
	}

	/**
	 * Returns true if a given Constraint is in the List of currently selected FeatureParts in the FeatureModel.
	 *
	 * @param constraint which is checked
	 * @return true if the given Constraint matches. False otherwise.
	 */
	private boolean constraintInSelection(IConstraint constraint) {
		for (final FeatureEditPart featureEditPart : selection) {
			if (matchesConstraint(featureEditPart, constraint)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Helper method for String comparison of a part and a constraint.
	 *
	 * @param part to compare with Constraint
	 * @param constraint to compare with the part
	 * @return true if the Strings of the Constraint and FeaturePart match each other. False otherwise.
	 */
	private boolean matchesConstraint(FeatureEditPart part, IConstraint constraint) {
		final IGraphicalFeature model = part.getModel();
		if (model == null) {
			return false;
		}
		final String partName = model.toString();
		final String constraintName = constraint.getDisplayName();
		return constraintName.matches(".*( |^)-*" + partName + "( |$).*");
	}

	public List<FeatureEditPart> getSelection() {
		return selection;
	}

	/**
	 * Clears the filter by removing any active explanation, selection, graphical feature model and search text.
	 */
	public void clear() {
		setActiveExplanation(null);
		setFeatureModelSelection(null);
		setSearchText("");
		setGraphicalFeatureModel(null);
	}
}
