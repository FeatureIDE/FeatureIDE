/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2012  FeatureIDE team, University of Magdeburg
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

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
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
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IPropertyListener;
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
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.outline.FmLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.FmTreeContentProvider;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.model.Class;
import de.ovgu.featureide.ui.views.collaboration.model.Role;

/**
 * Another outline view displaying the same information as the collaboration
 * diagram
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 */
/*
 * TODO #404 fix bug: do not close the tree if a corresponding file 
 * was opened with an other way e.g. via collaboration diagram
 * 
 * TODO Sometimes the outline has no content -> display a warning / message 
 * 
 */
public class CollaborationOutline extends ViewPart implements ICurrentBuildListener {

	private TreeViewer viewer;
	private IFile iFile;
	private IEditorPart active_editor;
	private UIJob uiJob;
	private CollaborationOutlineTreeContentProvider contentProvider = new CollaborationOutlineTreeContentProvider();
	private CollaborationOutlineLabelProvider clabel = new CollaborationOutlineLabelProvider();
	private FmTreeContentProvider modelContentProvider = new FmTreeContentProvider();
	private FmLabelProvider modelLabelProvider = new FmLabelProvider();
	private FmOutlinePageContextMenu contextMenu;

	private static final ImageDescriptor IMG_COLLAPSE = UIPlugin.getDefault()
			.getImageDescriptor("icons/collapse.gif");
	private static final ImageDescriptor IMG_EXPAND = UIPlugin.getDefault()
			.getImageDescriptor("icons/expand.gif");

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

		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setEditorActions(part);
		}

		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IEditorPart || part instanceof ViewPart)
				setEditorActions(part);
		}

	};

	private IPropertyListener plistener = new IPropertyListener() {
		@Override
		public void propertyChanged(Object source, int propId) {
			update(iFile);
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
				Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
				if (selection instanceof FSTMethod) {
					FSTMethod meth = (FSTMethod) selection;
					if (meth.isOwn(iFile)) {
						scrollToLine(active_editor, meth.getLineNumber(iFile));
					}
					return;
				} else if (selection instanceof FSTField) {
					FSTField field = (FSTField) selection;
					if (field.isOwn(iFile)) {
						scrollToLine(active_editor, field.getLineNumber(iFile));
					}
					return;
				} else if (selection instanceof FSTDirective) {
					FSTDirective directive = (FSTDirective) selection;
					scrollToLine(active_editor, directive.getStartLine(), directive.getEndLine(), 
							directive.getStartOffset(), directive.getEndLength());
					return;
				} else if (selection instanceof Role) {
						
	
					Role r = (Role) selection;
	
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
							iFile = r.file;
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
			}

		}

	};
	public CollaborationOutline() {
		super();
		CorePlugin.getDefault().addCurrentBuildListener(this);
	}

	/**
	 * handles all the editorActions
	 * 
	 * @param part
	 */
	private void setEditorActions(IWorkbenchPart activeEditor) {
		IEditorPart part = null;

		if (activeEditor != null) {
			IWorkbenchPage page = activeEditor.getSite().getPage();
			if (page != null) {
				part = page.getActiveEditor();
				if (part != null) {
					IEditorInput editorInput = part.getEditorInput();
					if (editorInput instanceof FileEditorInput) {
						active_editor = part;
						active_editor.addPropertyListener(plistener);
						// case: open editor
						FileEditorInput inputFile = (FileEditorInput) part
								.getEditorInput();
						IFeatureProject featureProject = CorePlugin.getFeatureProject(inputFile
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
		}
		// remove content from TreeViewer
		update(null);
	}

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.getControl().setEnabled(false);
		getSite().getPage().addPartListener(editorListener);

		viewer.setAutoExpandLevel(2);
		addToolbar(getViewSite().getActionBars().getToolBarManager());

		if (getSite().getPage().getActiveEditor() != null) {

			FileEditorInput inputFile = (FileEditorInput) getSite().getPage()
					.getActiveEditor().getEditorInput();

			IFeatureProject featureProject = CorePlugin.getFeatureProject(inputFile.getFile());

			if (featureProject != null)
				update(inputFile.getFile());
		}

		viewer.addTreeListener(treeListener);
		viewer.addSelectionChangedListener(selectionChangedListener);
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	/**
	 * Sets the new input or disables the viewer in case no editor is open
	 * 
	 * @param iFile2
	 */
	private void update(IFile iFile2) {
		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {
				if (refreshContent(iFile2)) {
					return;
				}
				iFile = iFile2;
				
				if (uiJob == null || uiJob.getState() == Job.NONE) {
					uiJob = new UIJob("Update Outline View") {
						public IStatus runInUIThread(IProgressMonitor monitor) {

							if (viewer != null) {
								if (viewer.getControl() != null
										&& !viewer.getControl().isDisposed()) {
									viewer.getControl().setRedraw(false);

									if (iFile != null) {
										if ("model.xml".equals(iFile.getName())
												&& active_editor instanceof FeatureModelEditor) {

											viewer.setContentProvider(modelContentProvider);
											viewer.setLabelProvider(modelLabelProvider);
											viewer.setInput(((FeatureModelEditor) active_editor)
													.getFeatureModel());
											
											//recreate the context menu in case we switched to another model
											if (contextMenu == null
													|| contextMenu
															.getFeatureModel() != ((FeatureModelEditor) active_editor)
															.getFeatureModel()) {
												if (contextMenu != null) {
													// the listener isn't recreated, if it still exists
													// but we need a new listener for the new model
													viewer.removeDoubleClickListener(contextMenu.dblClickListener);
												}
												contextMenu = new FmOutlinePageContextMenu(
														getSite(),
														(FeatureModelEditor) active_editor,
														viewer,
														((FeatureModelEditor) active_editor)
																.getFeatureModel());
											}

										} else {
											clabel.setFile(iFile);
											viewer.setContentProvider(contentProvider);
											viewer.setLabelProvider(clabel);
											viewer.setInput(iFile);
										}
									} else {
										// simply remove the content from the outline
										//case: no providers set
										if (viewer.getContentProvider() == null) {
											viewer.setContentProvider(contentProvider);
										}
										if (!(viewer.getLabelProvider() instanceof CollaborationOutlineLabelProvider)) {
											viewer.setLabelProvider(clabel);
										}
										viewer.setInput(null);
									}
									colorizeItems(viewer.getTree().getItems());
									viewer.getControl().setEnabled(
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
	}

	/**
	 * This method only updates the root and colors  
	 * @param iFile2 
	 * @return <code>false</code> if the content needs to be replaced
	 */
	private boolean refreshContent(IFile iFile2) {
		if (iFile2 != null && iFile != null) {
			/** only set the colors of the tree if the content is the same **/
			TreeItem[] items = viewer.getTree().getItems();
			if (iFile2.getName().equals(iFile.getName()) && items.length > 0) {
				TreeItem item = items[0];
				if (item != null) {
					if (item.getData() instanceof  Class) {
						if (!hasSameClass((Class) item.getData(), iFile2)) {
							return false;
						}
						iFile = iFile2;
						String toAppend = " - Composed class"; 
						for (Role r : ((Class)item.getData()).getRoles()) {
							if (r.directives.size() > 0) {
								toAppend =  "";
								break;
							}
							if (r.getRoleFile().equals(iFile)) {
								toAppend = " - " + r.featureName;
								break;
							}
						}
						item.setText(((Class)item.getData()).getName()+toAppend);
						colorizeItems(viewer.getTree().getItems());
						return true;
					}
				}
			}
		}
		return false;
	}

	/**
	 * @return <code>true</code> if the new input does not change the old content.
	 */
	private boolean hasSameClass(Class Class, IFile iFile2) {
		if (!iFile2.getProject().equals(iFile.getProject())) {
			return false;
		}
		if (isBuildFile(iFile2.getParent(), 
				CorePlugin.getFeatureProject(iFile2).getBuildFolder())) {
			return true;
		}
		if (isBuildFile(iFile.getParent(), 
				CorePlugin.getFeatureProject(iFile).getBuildFolder())) {
			return true;
		}
		
		if (iFile2.equals(iFile)) {
			return true;
		}
		boolean i = false;
		boolean j = false;
		for (Role role : Class.getRoles()) {
			if (role.getRoleFile().equals(iFile)) {
				i = true;
			} else if (role.getRoleFile().equals(iFile2)) {
				j = true;
			}
		}
		return j && i;
	}

	/**
	 * @param parent
	 * @param buildFolder
	 * @return <code>true</code> if the build folder contains the given folder
	 */
	private boolean isBuildFile(IContainer parent, IFolder buildFolder) {
		if (parent == null) {
			return false;
		}
		if (parent instanceof IFolder) {
			if (parent.equals(buildFolder)) {
				return true;
			}
			return isBuildFile(parent.getParent(), buildFolder);
		}
		return false;
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
				} else {
					treeItems[i].setForeground(viewer.getControl().getDisplay()
							.getSystemColor(SWT.DEFAULT));
				}
			} else if (treeItems[i].getData() instanceof FSTField) {
				if (!((FSTField) treeItems[i].getData()).isOwn(iFile)) {
					treeItems[i].setForeground(viewer.getControl().getDisplay()
							.getSystemColor(SWT.COLOR_GRAY));
				} else {
					treeItems[i].setForeground(viewer.getControl().getDisplay()
							.getSystemColor(SWT.DEFAULT));
				}
			} else if (treeItems[i].getData() instanceof Role) {
				if (((Role) treeItems[i].getData()).file.equals(iFile)) {
					// get old Font and simply make it bold
					treeItems[i].setFont(new Font(treeItems[i].getDisplay(),
									treeItems[i].getFont().getFontData()[0]
											.getName(), treeItems[i].getFont()
											.getFontData()[0].getHeight(),
									SWT.BOLD));
				} else {
					treeItems[i].setFont(new Font(treeItems[i].getDisplay(),
						treeItems[i].getFont().getFontData()[0].getName(), 
						treeItems[i].getFont().getFontData()[0].getHeight(),
									0));
				}
			}
		}
	}

	/**
	 * provides functionality to expand and collapse all items in viewer
	 * 
	 * @param iToolBarManager
	 */
	public void addToolbar(IToolBarManager iToolBarManager) {
		Action collapseAllAction = new Action() {
			public void run() {
				viewer.collapseAll();
				viewer.expandToLevel(2);
				viewer.refresh();
			}
		};
		collapseAllAction.setToolTipText("Collapse All");
		collapseAllAction.setImageDescriptor(IMG_COLLAPSE);

		Action expandAllAction = new Action() {
			public void run() {
				viewer.expandAll();
				// treeExpanded event is not triggered, so we manually have to
				// call this function
				colorizeItems(viewer.getTree().getItems());
			}
		};
		expandAllAction.setToolTipText("Expand All");
		expandAllAction.setImageDescriptor(IMG_EXPAND);

		iToolBarManager.add(collapseAllAction);
		iToolBarManager.add(expandAllAction);
	}

	/**
	 * Jumps to a line in the given editor
	 * 
	 * @param editorPart
	 * @param lineNumber
	 */
	public static void scrollToLine(IEditorPart editorPart, int lineNumber) {
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
				editor.selectAndReveal(lineInfo.getOffset(), lineInfo.getLength());
			}
		}
	}
	
	/**
	 * Highlights the whole if-Block for a FSTDirective
	 * 
	 * @param editorPart
	 * @param startLine the first line of a directive
	 * @param endLine the last line of a directive
	 * @param startOffset characters before the statement starts
	 * @param endOffset length of the last line
	 */
	public static void scrollToLine(IEditorPart editorPart, int startLine, int endLine, int startOffset, int endOffset) {
		if (!(editorPart instanceof ITextEditor) || startLine < 0 || endLine < 0) {
			return;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		IDocument document = editor.getDocumentProvider().getDocument(
				editor.getEditorInput());
		if (document != null) {
			try {
				int offset = document.getLineOffset(startLine)+startOffset;
				editor.selectAndReveal(offset, document.getLineOffset(endLine) - (offset) + endOffset);
			} catch (BadLocationException e) {
			}
		}
	}

	/* (non-Javadoc)
	 * @see de.ovgu.featureide.core.listeners.ICurrentBuildListener#updateGuiAfterBuild(de.ovgu.featureide.core.IFeatureProject)
	 */
	@Override
	public void updateGuiAfterBuild(IFeatureProject project, IFile configurationFile) {
		if (iFile != null && project.equals(CorePlugin.getFeatureProject(iFile))) {
			IFile iFile2 = iFile;
			iFile = null;
			update(iFile2);
		}
	}
}