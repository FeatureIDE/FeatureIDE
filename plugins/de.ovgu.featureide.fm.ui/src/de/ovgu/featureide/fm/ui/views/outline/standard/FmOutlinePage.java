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
package de.ovgu.featureide.fm.ui.views.outline.standard;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.custom.OutlineLabelProvider;

/**
 * This class is part of the outline. It sets up an new outline page that uses a
 * TreeView to show the FeatureModel currently being worked on.
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

	private FmOutlinePageContextMenu contextMenu;
	
	private IFile iFile;

	public FmOutlinePage(IDocumentProvider documentProvider, FeatureModelEditor editor) {
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
	public void setInput(IFeatureModel input) {
		fInput = input;
		update(((FileEditorInput) fTextEditor.getEditorInput()).getFile());
	}

	/**
	 * Sets the new input or disables the viewer in case no editor is open
	 * 
	 */
	private void update(IFile iFile2) {
		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {

				iFile = iFile2;
				
				if (viewer != null) {
					if (viewer.getControl() != null && !viewer.getControl().isDisposed()) {
						viewer.getControl().setRedraw(false);

						viewer.setContentProvider(new FmTreeContentProvider());
						viewer.setLabelProvider(new FMOutlineLabelProviderWrapper());
						if (iFile != null) {
							if ("xml".equalsIgnoreCase(iFile.getFileExtension()) && fTextEditor.getEditorInput() instanceof FeatureModelEditor) {

								// recreate the context menu in case
								// we switched to another model
								if (contextMenu == null || contextMenu.getFeatureModel() != ((FeatureModelEditor) fTextEditor.getEditorInput()).getFeatureModel()) {
									if (contextMenu != null) {
										// the listener isn't
										// recreated, if it still
										// exists
										// but we need a new
										// listener for the new
										// model
										viewer.removeDoubleClickListener(contextMenu.dblClickListener);
									}
									contextMenu = new FmOutlinePageContextMenu(getSite(), (FeatureModelEditor) fTextEditor.getEditorInput(), viewer,
											((FeatureModelEditor) fTextEditor.getEditorInput()).getFeatureModel(), false);
								}
							} else {
								viewer.setInput(iFile);
							}
						} else {
							viewer.setInput("");
						}

						if (viewer.getLabelProvider() instanceof OutlineLabelProvider && iFile != null) {
							((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), iFile);

							viewer.getContentProvider().inputChanged(viewer, null, iFile);
						}

						viewer.getControl().setRedraw(true);
						viewer.getControl().setEnabled(true);
						viewer.refresh();

					}
				}
			}
		}
	}

	public void createControl(Composite parent) {
		super.createControl(parent);
		if (viewer == null) {
			viewer = getTreeViewer();
			FmTreeContentProvider fmTreeContentProvider = new FmTreeContentProvider();
			fmTreeContentProvider.setGraphicalFeatureModel(fTextEditor.diagramEditor.getGraphicalFeatureModel());
			viewer.setContentProvider(fmTreeContentProvider);
			viewer.setLabelProvider(new FmLabelProvider());
		}

		if (fInput != null && fInput.getStructure().getRoot() != null) {
			viewer.setInput(fInput);
		}

		viewer.expandToLevel(2);
		FmOutlinePageContextMenu cm = new FmOutlinePageContextMenu(getSite(), fTextEditor, viewer, fInput);
		cm.addToolbar(getSite().getActionBars().getToolBarManager());
	}
	
}
