/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2013  FeatureIDE team, University of Magdeburg, Germany
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
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.fm.ui.views.outline;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;

/**
 * This class is part of the outline. It sets up an new outline page that uses a
 * TreeView to show the FeatureModel currently being worked on.
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
/*
 * TODO #404 fix bug: tree minimizes after selecting the editor page
 */
public class FmOutlinePage extends ContentOutlinePage {

	protected FeatureModel fInput;

	protected IDocumentProvider fDocumentProvider;

	protected FeatureModelEditor fTextEditor;

	private TreeViewer viewer;

	private Object[] expandedElements;

	public FmOutlinePage(IDocumentProvider documentProvider,
			FeatureModelEditor editor) {
		super();

		fDocumentProvider = documentProvider;
		fTextEditor = editor;
	}

	/**
	 * Sets the input of the outline page
	 * 
	 * @param input
	 *            the input of this outline page
	 */
	public void setInput(FeatureModel input) {
		fInput = input;
		update();
	}

	/**
	 * Updates the outline page.
	 */
	public void update() {
		if(fInput==null||fInput.getRoot()==null)return;
		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {
				expandedElements = viewer.getExpandedElements();
				control.setRedraw(false);
				viewer.setInput(fInput);
				viewer.setExpandedElements(expandedElements);
				control.setRedraw(true);
			}
		}
	}

	public void createControl(Composite parent) {
		super.createControl(parent);
		if (viewer == null) {
			viewer = getTreeViewer();
			viewer.setContentProvider(new FmTreeContentProvider());
			viewer.setLabelProvider(new FmLabelProvider());
		}

		if (fInput != null&&fInput.getRoot()!=null) {
			viewer.setInput(fInput);
		}
		
		viewer.expandToLevel(2);
		FmOutlinePageContextMenu cm = new FmOutlinePageContextMenu(getSite(),fTextEditor,viewer,fInput);
		cm.addToolbar(getSite().getActionBars().getToolBarManager());
	}
}
