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
 * See http://featureide.cs.ovgu.de/ for further information.
 */
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
		if (parentElement instanceof CloneAnalysisResults) return ((CloneAnalysisResults<?>) parentElement).getClones().toArray();
		if (parentElement instanceof Clone) return ((Clone) parentElement).getOccurences().toArray();
		return new Object[0];
	}

	@Override
	public Object getParent(Object element) {
		if (element instanceof Clone) return this.cloneAnalysisView.results;
		if (element instanceof CloneOccurence) return ((CloneOccurence) element).getClone();
		return null;
	}

	@Override
	public boolean hasChildren(Object element) {
		if (element instanceof List) return ((List<?>) element).size() > 0;

		assert (!(element instanceof Clone)
			|| ((element instanceof Clone) && ((Clone) element).getOccurences().size() > 0)) : "Clones without occurences make no sense";

		return (element instanceof Clone);
	}

	@Override
	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	@Override
	public void dispose() {}

	@Override
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {}
}
