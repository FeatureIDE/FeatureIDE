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
package de.ovgu.featureide.fm.ui.views.outline;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

/**
 * This class is part of the outline. It sets up an new outline page that uses a TreeView to show the FeatureModel currently being worked on.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke
 */
/*
 * TODO #404 fix bug: tree minimizes after selecting the editor page
 */
public class FmOutlinePage extends ContentOutlinePage {

	protected IFeatureModel fInput;

	protected IDocumentProvider fDocumentProvider;

	protected FeatureModelEditor fTextEditor;

	private TreeViewer viewer;

	private Object[] expandedElements;

	public FmOutlinePage(IDocumentProvider documentProvider, FeatureModelEditor editor) {
		super();

		fDocumentProvider = documentProvider;
		fTextEditor = editor;
	}

	/**
	 * Sets the input of the outline page
	 *
	 * @param input the input of this outline page
	 */
	public void setInput(IFeatureModel input) {
		fInput = input;
		update();
	}

	/**
	 * Updates the outline page.
	 */
	public void update() {
		if ((fInput == null) || (fInput.getStructure().getRoot() == null)) {
			return;
		}
		if (viewer != null) {
			final Control control = viewer.getControl();
			if ((control != null) && !control.isDisposed()) {
				expandedElements = viewer.getExpandedElements();
				control.setRedraw(false);
				viewer.setInput(fInput);
				viewer.setExpandedElements(expandedElements);
				control.setRedraw(true);
			}
		}
	}

	@Override
	public void createControl(Composite parent) {
		super.createControl(parent);
		if (viewer == null) {
			viewer = getTreeViewer();
			final FmTreeContentProvider fmTreeContentProvider = new FmTreeContentProvider();
			fmTreeContentProvider.setGraphicalFeatureModel(fTextEditor.diagramEditor.getGraphicalFeatureModel());
			viewer.setContentProvider(fmTreeContentProvider);
			viewer.setLabelProvider(new FmLabelProvider());
		}

		if ((fInput != null) && (fInput.getStructure().getRoot() != null)) {
			viewer.setInput(fInput);
		}

		viewer.expandToLevel(2);
		final FmOutlinePageContextMenu cm = new FmOutlinePageContextMenu(getSite(), fTextEditor, viewer, fInput);
		cm.addToolbar(getSite().getActionBars().getToolBarManager());
	}
}
