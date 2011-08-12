/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2011  FeatureIDE Team, University of Magdeburg
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program. If not, see http://www.gnu.org/licenses/.
 *
 * See http://www.fosd.de/featureide/ for further information.
 */
package de.ovgu.featureide.ui.views.collaboration.outline;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeViewerListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;
import org.eclipse.ui.texteditor.ITextEditor;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.editors.ConfigurationEditor;
import de.ovgu.featureide.ui.views.collaboration.model.Role;

/**
 * 
 * another outline view displaying the same information as the collaboration
 * diagram
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
public class CollaborationOutline extends ViewPart {

	private TreeViewer viewer;
	private IFile iFile;
	private IFeatureProject featureProject;
	private Object[] expandedElements;
	private IEditorPart active_editor;
	public static final String ID = UIPlugin.PLUGIN_ID
			+ ".views.collaboration.outline.CollaborationOutline";

	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

	};

	/**
	 * opens the corresponding role on double click
	 */
	private IDoubleClickListener dblClicklistener = new IDoubleClickListener() {

		@Override
		public void doubleClick(DoubleClickEvent event) {
			if (!(((IStructuredSelection) viewer.getSelection())
					.getFirstElement() instanceof Role))
				return;

			Role r = (Role) ((IStructuredSelection) viewer.getSelection())
					.getFirstElement();

			if (r.file.isAccessible()) {
				IWorkbenchWindow window = PlatformUI.getWorkbench()
						.getActiveWorkbenchWindow();
				IWorkbenchPage page = window.getActivePage();
				IContentType contentType = null;
				try {
					IContentDescription description = r.file
							.getContentDescription();
					if (description != null) {
						contentType = description.getContentType();
					}
					IEditorDescriptor desc = null;
					if (contentType != null) {
						desc = PlatformUI
								.getWorkbench()
								.getEditorRegistry()
								.getDefaultEditor(r.file.getName(), contentType);
					} else {
						desc = PlatformUI.getWorkbench().getEditorRegistry()
								.getDefaultEditor(r.file.getName());
					}

					if (desc != null) {
						page.openEditor(new FileEditorInput(r.file),
								desc.getId());
					} else {
						// case: there is no default editor for the file
						page.openEditor(new FileEditorInput(r.file),
								"org.eclipse.ui.DefaultTextEditor");
					}
				} catch (CoreException e) {
					UIPlugin.getDefault().logError(e);
				}
			}

		}

	};
	/**
	 * colors the tree in case a treeItem has been expanded (because the
	 * children are lazily loaded)
	 */
	private ITreeViewerListener treeListener = new ITreeViewerListener() {

		@Override
		public void treeCollapsed(TreeExpansionEvent event) {
		}

		@Override
		public void treeExpanded(TreeExpansionEvent event) {
			colorizeItems(viewer.getTree().getItems());
		}

	};

	/**
	 * triggers a scrolling action to the selected field/method in the current
	 * editor
	 */
	private ISelectionChangedListener selectionChangedListener = new ISelectionChangedListener() {
		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			if (iFile != null) {
				if ((((IStructuredSelection) viewer.getSelection())
						.getFirstElement() instanceof FSTMethod)) {
					FSTMethod meth = (FSTMethod) ((IStructuredSelection) viewer
							.getSelection()).getFirstElement();
					if (meth.isOwn(iFile)) {
						scrollToLine(active_editor, meth.getLineNumber(iFile));
					}
				} else if ((((IStructuredSelection) viewer.getSelection())
						.getFirstElement() instanceof FSTField)) {
					FSTField field = (FSTField) ((IStructuredSelection) viewer
							.getSelection()).getFirstElement();
					if (field.isOwn(iFile)) {
						scrollToLine(active_editor, field.getLineNumber(iFile));
					}
				}
			}

		}

	};

	public CollaborationOutline() {
		super();
	}

	/**
	 * handles all the editorActions
	 * 
	 * @param part
	 */
	private void setEditorActions(IWorkbenchPart activeEditor) {
		IEditorPart part = null;
		if (activeEditor != null
				&& !(activeEditor instanceof FeatureModelEditor)
				&& !(activeEditor instanceof ConfigurationEditor)) {
			IWorkbenchPage page = activeEditor.getSite().getPage();
			if (page != null) {
				part = page.getActiveEditor();
				if (part != null) {
					this.active_editor = part;
					// case: open editor
					FileEditorInput inputFile = (FileEditorInput) part
							.getEditorInput();
					featureProject = CorePlugin.getFeatureProject(inputFile
							.getFile());
					if (featureProject != null) {
						Control control = viewer.getControl();
						if (control != null && !control.isDisposed()) {
							update(inputFile.getFile());
						}
						return;
					}
				}
			}
		}
		// remove content from TreeViewer
		update(null);
	}

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.getControl().setEnabled(false);
		getSite().getPage().addPartListener(editorListener); // EditorListener

		viewer.setContentProvider(new CollaborationOutlineTreeContentProvider());
		viewer.setLabelProvider(new CollaborationOutlineLabelProvider());
		viewer.setAutoExpandLevel(2);
		viewer.addDoubleClickListener(dblClicklistener);
		viewer.addTreeListener(treeListener);
		viewer.addSelectionChangedListener(selectionChangedListener);
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	/**
	 * sets the new input or disables the viewer in case no editor is open
	 * 
	 * @param iFile
	 */
	public void update(IFile iFile) {
		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {
				this.iFile = iFile;
				UIJob uiJob = new UIJob("Create Outline View") {
					public IStatus runInUIThread(IProgressMonitor monitor) {
						if (viewer != null) {
							if (viewer.getControl() != null
									&& !viewer.getControl().isDisposed()) {
								expandedElements = viewer.getExpandedElements();
								viewer.getControl().setRedraw(false);
								viewer.setInput(CollaborationOutline.this.iFile);
								viewer.setExpandedElements(expandedElements);
								viewer.expandToLevel(2);
								colorizeItems(viewer.getTree().getItems());
								viewer.getControl()
										.setEnabled(
												CollaborationOutline.this.iFile != null);
								viewer.refresh();
								viewer.getControl().setRedraw(true);
							}
						}
						return Status.OK_STATUS;
					}
				};
				uiJob.setPriority(Job.SHORT);
				uiJob.schedule();
			}
		}
	}

	/**
	 * colors the TreeItems gray in case the method/field is not in the current
	 * file<br>
	 * makes the TreeItems bold in case the Feature inside the TreeItem is in
	 * the current file
	 * 
	 * @param treeItems
	 *            the items that should be colored
	 */
	private void colorizeItems(TreeItem[] treeItems) {
		for (int i = 0; i < treeItems.length; i++) {
			if (treeItems[i].getItems().length > 0) {
				colorizeItems(treeItems[i].getItems());
			}

			if (treeItems[i].getData() instanceof FSTMethod) {
				if (!((FSTMethod) treeItems[i].getData()).isOwn(iFile)) {
					treeItems[i].setForeground(viewer.getControl().getDisplay()
							.getSystemColor(SWT.COLOR_GRAY));
				}
			} else if (treeItems[i].getData() instanceof FSTField) {
				if (!((FSTField) treeItems[i].getData()).isOwn(iFile)) {
					treeItems[i].setForeground(viewer.getControl().getDisplay()
							.getSystemColor(SWT.COLOR_GRAY));
				}
			} else if (treeItems[i].getData() instanceof Role) {
				if (((Role) treeItems[i].getData()).file.equals(iFile)) {
					// get old Font and simply make it bold
					treeItems[i]
							.setFont(new Font(treeItems[i].getDisplay(),
									treeItems[i].getFont().getFontData()[0]
											.getName(), treeItems[i].getFont()
											.getFontData()[0].getHeight(),
									SWT.BOLD));
				}
			}
		}
	}

	/**
	 * Jumps to a line in the given editor
	 * 
	 * @param editorPart
	 * @param lineNumber
	 */
	private static void scrollToLine(IEditorPart editorPart, int lineNumber) {
		if (!(editorPart instanceof ITextEditor) || lineNumber <= 0) {
			return;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		IDocument document = editor.getDocumentProvider().getDocument(
				editor.getEditorInput());
		if (document != null) {
			IRegion lineInfo = null;
			try {
				lineInfo = document.getLineInformation(lineNumber - 1);
			} catch (BadLocationException e) {
			}
			if (lineInfo != null) {
				editor.selectAndReveal(lineInfo.getOffset(),
						lineInfo.getLength());
			}
		}
	}
}