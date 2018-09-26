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
package de.ovgu.featureide.fm.ui.editors.featuremodel.actions;

import static de.ovgu.featureide.fm.core.localization.StringTable.SELECT_SUBTREE;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureStructure;
import de.ovgu.featureide.fm.ui.editors.IGraphicalFeatureModel;

/**
 * Selects the whole subtree of a selected feature
 *
 * @author Sabrina Hugo
 * @author Christian Orsinger
 */
public class SelectSubtreeAction extends SingleSelectionAction {

	public static final String ID = "de.ovgu.featureide.selectSubtree";
	private final IGraphicalFeatureModel graphicalFeatureModel;
	private IStructuredSelection selection;

	/**
	 * @param text
	 * @param viewer
	 * @param id
	 */
	public SelectSubtreeAction(Object viewer, IGraphicalFeatureModel graphicalFeatureModel) {
		super(SELECT_SUBTREE, viewer, ID);
		this.graphicalFeatureModel = graphicalFeatureModel;
	}

	@Override
	public void run() {
		if (viewer instanceof TreeViewer) {
			final List<IFeature> children = new ArrayList();
			children.add(feature);
			for (final IFeatureStructure struct : feature.getStructure().getChildren()) {
				children.add(struct.getFeature());
			}
		}

	}

	@Override
	protected boolean isValidSelection(IStructuredSelection selection) {
		this.selection = selection;
		return super.isValidSelection(selection);
	}

	@Override
	protected void updateProperties() {
		setEnabled(true);
	}

}
