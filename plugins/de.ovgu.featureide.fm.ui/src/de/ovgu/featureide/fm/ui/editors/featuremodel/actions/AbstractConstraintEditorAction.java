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

import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeViewer;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.ConstraintDialog;

/**
 * Basic implementation for actions on constraints.
 *
 * @author Christian Becker
 * @author Thomas Thuem
 * @author Marcus Pinnecke (Feature Interface)
 */
public abstract class AbstractConstraintEditorAction extends AFeatureModelAction {

	protected Object viewer;
	protected IStructuredSelection selection;

	private final ISelectionChangedListener listener = new ISelectionChangedListener() {
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			setSelection(event.getSelection());
		}
	};

	public AbstractConstraintEditorAction(Object viewer, IFeatureModelManager featureModelManager, String menuname, String id) {
		super(menuname, id, featureModelManager);
		this.viewer = viewer;
		if (viewer instanceof TreeViewer) {
			((TreeViewer) viewer).addSelectionChangedListener(listener);
			setSelection(((TreeViewer) viewer).getSelection());
		} else if (viewer instanceof GraphicalViewerImpl) {
			((GraphicalViewerImpl) viewer).addSelectionChangedListener(listener);
			setSelection(((GraphicalViewerImpl) viewer).getSelection());
		} else {
			setSelection(null);
		}
	}

	protected void setSelection(final ISelection viewerSelection) {
		selection = (viewerSelection instanceof IStructuredSelection) ? (IStructuredSelection) viewerSelection : null;
		setEnabled(isValidSelection(selection));
	}

	protected void openEditor(IConstraint constraint) {
		new ConstraintDialog(featureModelManager, constraint);
	}

	protected abstract boolean isValidSelection(IStructuredSelection selection);

}
