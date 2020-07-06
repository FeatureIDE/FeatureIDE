package de.ovgu.featureide.fm.ui.views.constraintview.content;

import org.eclipse.jface.viewers.ITreeContentProvider;

import de.ovgu.featureide.fm.core.base.IFeatureModel;

/**
 * This class is the ContentProvider for the Tree in the ConstraintView. Takes the FeatureModel and displays its Constraints together with their descriptions.
 *
 * @author Soeren Viegener
 * @author Philipp Vulpius
 */
public class ConstraintViewContentProvider implements ITreeContentProvider {

	/**
	 * This method returns the Constraints of a given FeatureModel as array to display in a TreeViewer.
	 *
	 * @param inputElement usually a FeatureModel.
	 * @return the Constraints of a given FeatureModel as array, or a String in special case.
	 */
	@Override
	public Object[] getElements(Object inputElement) {
		// called with the String "open a Feature Diagram" if no FeatureModel is open currently.
		if (inputElement instanceof String) {
			return new String[] { (String) inputElement };
		} else {
			final IFeatureModel featureModel = (IFeatureModel) inputElement;
			return featureModel.getConstraints().toArray();
		}
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		return false;
	}

}
