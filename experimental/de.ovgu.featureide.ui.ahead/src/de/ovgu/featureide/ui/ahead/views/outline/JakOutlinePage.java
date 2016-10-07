/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2016  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.ui.ahead.views.outline;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.ovgu.featureide.ui.ahead.editors.JakEditor;
import de.ovgu.featureide.ui.ahead.views.outline.jak.JakLabelProvider;
import de.ovgu.featureide.ui.ahead.views.outline.jak.JakTreeContentProvider;

/**
 * This class is part of the outline. It sets up an new outline page
 * that uses a TreeView to show a part of the jakproject model that
 * has to do with the currently visible file in the text editor.
 * 
 * @author Tom Brosch
 *
 */
public class JakOutlinePage extends ContentOutlinePage {

	protected Object fInput;

	protected IDocumentProvider fDocumentProvider;

	protected JakEditor fTextEditor;

	public JakOutlinePage(IDocumentProvider documentProvider, JakEditor editor) {
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
	public void setInput(Object input) {
		fInput = input;
		update();
	}

	/**
	 * Updates the outline page.
	 */
	public void update() {
		TreeViewer viewer = getTreeViewer();

		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {
				control.setRedraw(false);
				viewer.setInput(fInput);
				viewer.expandAll();
				control.setRedraw(true);
			}
		}
	}

	public void createControl(Composite parent) {
		super.createControl(parent);
		TreeViewer viewer = getTreeViewer();
		viewer.setContentProvider(new JakTreeContentProvider());
		viewer.setLabelProvider(new JakLabelProvider());
		viewer.addSelectionChangedListener(this);
		if (fInput != null)
			viewer.setInput(fInput);
		viewer.expandAll();
	}
}
