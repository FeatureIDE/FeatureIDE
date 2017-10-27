package de.ovgu.featureide.cloneanalysis.views;

import java.util.List;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

import de.ovgu.featureide.cloneanalysis.impl.CloneOccurence;
import de.ovgu.featureide.cloneanalysis.results.Clone;
import de.ovgu.featureide.cloneanalysis.results.CloneAnalysisResults;

class CloneAnalysisContentProvider implements ITreeContentProvider {

	/**
	 * 
	 */
	private final CloneAnalysisView cloneAnalysisView;

	/**
	 * @param cloneAnalysisView
	 */
	CloneAnalysisContentProvider(CloneAnalysisView cloneAnalysisView) {
		this.cloneAnalysisView = cloneAnalysisView;
	}

	@Override
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof CloneAnalysisResults)
			return ((CloneAnalysisResults<?>) parentElement).getClones().toArray();
		if (parentElement instanceof Clone)
			return ((Clone) parentElement).getOccurences().toArray();
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof Clone)
			return this.cloneAnalysisView.results;
		if (element instanceof CloneOccurence)
			return ((CloneOccurence) element).getClone();
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof List)
			return ((List<?>) element).size() > 0;

		assert (!(element instanceof Clone) || ((element instanceof Clone)
				&& ((Clone) element).getOccurences().size() > 0)) : "Clones without occurences make no sense";

		return (element instanceof Clone);
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	@Override
	public void dispose() {
	}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
	}
}