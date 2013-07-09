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
package de.ovgu.featureide.ui.mpl.views.outline;

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
import org.eclipse.ui.IWorkbench;
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
import de.ovgu.featureide.core.fstmodel.FSTClass;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.core.mpl.MPLPlugin;
import de.ovgu.featureide.core.mpl.signature.ProjectSignature;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractClassFragment;
import de.ovgu.featureide.core.mpl.signature.abstr.AbstractSignature;
import de.ovgu.featureide.ui.mpl.MPLUIPlugin;
//import de.ovgu.featureide.ui.views.collaboration.outline.CollaborationOutlineLabelProvider;

/**
 * Another outline view displaying the same information as the collaboration
 * diagram
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Reimar Schröter
 */
/*
 * TODO #404 fix bug: do not close the tree if a corresponding file 
 * was opened with an other way e.g. via collaboration diagram
 * 
 * TODO Sometimes the outline has no content -> display a warning / message 
 * 
 */
public class CollOutline extends ViewPart implements ICurrentBuildListener {

	private TreeViewer viewer;
	private IFile iFile;
	private IEditorPart active_editor;
	private UIJob uiJob;
	private CollaborationOutlineTreeContentProvider contentProvider = new CollaborationOutlineTreeContentProvider();
	private CollaborationOutlineLabelProvider clabel = new CollaborationOutlineLabelProvider();


	private static final ImageDescriptor IMG_COLLAPSE = MPLUIPlugin.getDefault().getImageDescriptor("icons/FeatureProjectDecorator.png");
	private static final ImageDescriptor IMG_EXPAND = MPLUIPlugin.getDefault().getImageDescriptor("icons/FeatureProjectDecorator.png");

	public static final String ID = "de.ovgu.mpl"
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
					int line = getMethodLine(iFile, meth);
					if (line != -1) {
						scrollToLine(active_editor, line);
					}
				} else if (selection instanceof FSTField) {
					FSTField field = (FSTField) selection;
					int line = getFieldLine(iFile, field);
					if (line != -1) {
						scrollToLine(active_editor, line);
					}
				} else if (selection instanceof FSTDirective) {
					FSTDirective directive = (FSTDirective) selection;
					scrollToLine(active_editor, directive.getStartLine(), directive.getEndLine(), 
							directive.getStartOffset(), directive.getEndLength());
				} else if (selection instanceof FSTRole) {
					FSTRole r = (FSTRole) selection;
					if (r.getFile().isAccessible()) {
						IWorkbench workbench = PlatformUI
								.getWorkbench();
						IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
						IWorkbenchPage page = window.getActivePage();
						IContentType contentType = null;
						try {
							iFile = r.getFile();
							IContentDescription description = iFile
									.getContentDescription();
							if (description != null) {
								contentType = description.getContentType();
							}
							IEditorDescriptor desc = null;
							if (contentType != null) {
								desc = workbench.getEditorRegistry()
										.getDefaultEditor(iFile.getName(), contentType);
							} else {
								desc = workbench.getEditorRegistry()
										.getDefaultEditor(iFile.getName());
							}
							if (desc != null) {
								page.openEditor(new FileEditorInput(iFile),
										desc.getId());
							} else {
								// case: there is no default editor for the file
								page.openEditor(new FileEditorInput(iFile),
										"org.eclipse.ui.DefaultTextEditor");
							}
						} catch (CoreException e) {
							MPLUIPlugin.getDefault().logError(e);
						}
					}
				}
			}

		}

		// TODO refactor into FSTModel
		private int getFieldLine(IFile iFile, FSTField field) {
			for (FSTRole r : field.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTField f : r.getFields()) {
						if (f.comparesTo(field)) {
							return f.getLine();
						}
					}
				}
			}
			return -1;
		}

		private int getMethodLine(IFile iFile, FSTMethod meth) {
			for (FSTRole r : meth.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTMethod m : r.getMethods()) {
						if (m.comparesTo(meth)) {
							return m.getLine();
						}
					}
				}
			}
			return -1;
		}

	};
	
	public CollOutline() {
		super();
		CorePlugin.getDefault().addCurrentBuildListener(this);
	}

	/**
	 * handles all the editorActions
	 * 
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
						IFile file = inputFile.getFile();
						IFeatureProject featureProject = CorePlugin.getFeatureProject(file);
	
						if (featureProject != null) {
							Control control = viewer.getControl();
							if (control != null && !control.isDisposed()) {
								update(file);
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
		IWorkbenchPage page = getSite().getPage();
		page.addPartListener(editorListener);

		viewer.setAutoExpandLevel(2);
		addToolbar(getViewSite().getActionBars().getToolBarManager());

		IEditorPart activeEditor = page.getActiveEditor();
		if (activeEditor != null) {
			IFile inputFile = ((FileEditorInput) activeEditor.getEditorInput()).getFile();
			IFeatureProject featureProject = CorePlugin.getFeatureProject(inputFile);
			if (featureProject != null)
				update(inputFile);
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
	 */
	private void update(IFile iFile2) {

		IFeatureProject featureProject = CorePlugin.getFeatureProject(iFile2);
		
		if(featureProject ==  null || !MPLPlugin.getDefault().isInterfaceProject(iFile2.getProject()))
			return;
			
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
										clabel.setFile(iFile);
										viewer.setContentProvider(contentProvider);
										viewer.setLabelProvider(clabel);
										viewer.setInput(iFile);
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
													CollOutline.this.iFile != null);
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
	 * @return <code>false</code> if the content needs to be replaced
	 */
	private boolean refreshContent(IFile iFile2) {
		if (iFile2 != null && iFile != null) {
			/** only set the colors of the tree if the content is the same **/
			TreeItem[] items = viewer.getTree().getItems();
			if (iFile2.getName().equals(iFile.getName()) && items.length > 0) {
				TreeItem item = items[0];
				if (item != null) {
					if (item.getData() instanceof FSTClass) {
						if (!hasSameClass((FSTClass) item.getData(), iFile2)) {
							return false;
						}
						iFile = iFile2;
						String toAppend = " - Composed class"; 
						for (FSTRole r : ((FSTClass)item.getData()).getRoles()) {
							if (!r.getDirectives().isEmpty()) {
								toAppend =  "";
								break;
							}
							if (r.getFile().equals(iFile)) {
								toAppend = " - " + r.getFeature().getName();
								break;
							}
						}
						item.setText(((FSTClass)item.getData()).getName()+toAppend);
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
	private boolean hasSameClass(FSTClass Class, IFile iFile2) {
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
		for (FSTRole role : Class.getRoles()) {
			if (role.getFile().equals(iFile)) {
				i = true;
			} else if (role.getFile().equals(iFile2)) {
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
			if (treeItems[i].getData() instanceof RoleElement) {
				setForeground(treeItems[i]);
			} else if (treeItems[i].getData() instanceof FSTRole) {
				if (((FSTRole) treeItems[i].getData()).getFile().equals(iFile)) {
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
			if (treeItems[i].getItems().length > 0) {
				colorizeItems(treeItems[i].getItems());
			}
		}
	}

	ProjectSignature l=  null;
	String oldFeature = null;
	//TODO
	private void setForeground(TreeItem item) {
		RoleElement element = (RoleElement) item.getData();
		
		iFile.getProject();
		
		IFeatureProject featureProject = CorePlugin.getFeatureProject(iFile);
		
		
//		if(featureProject ==  null || !MPLPlugin.getDefault().isInterfaceProject(file.getProject()))
//			return new ArrayList<>();

		String featureName = featureProject.getFeatureName(iFile);	
		
		
		if(l==null || oldFeature == null || oldFeature.compareTo(featureName)!=0){
			oldFeature = featureName;
			l= MPLPlugin.getDefault().extendedModules_getSig(featureProject, featureName);
		}
		
		
		if (element instanceof FSTMethod) {
			FSTClass cl =  element.getRole().getFSTClass();
			if(cl instanceof FSTClass){
				AbstractClassFragment frag = l.getClass(cl.getRoles().get(0).getPackage() + "." + cl.getName().replace(".java", ""));
				for (AbstractSignature curSig : frag.getMembers()) {
					if(curSig.getName().compareTo(element.getName()) == 0){
						//TODO Parameter testen
						item.setForeground(viewer.getControl().getDisplay()
								.getSystemColor(SWT.DEFAULT));
						return;
					}
				}
			}
//			for (FSTMethod method : role.getMethods()) {
//				if (method.comparesTo(element)) {
//					item.setForeground(viewer.getControl().getDisplay()
//							.getSystemColor(SWT.DEFAULT));
//					return;
//				}
//			}
		}
		
		
//		for (FSTRole role : element.getRole().getFSTClass().getRoles()) {
//			if (!role.getFile().equals(iFile)) {
//				continue;
//			}
//			if (element instanceof FSTMethod) {
//				for (FSTMethod method : role.getMethods()) {
//					if (method.comparesTo(element)) {
//						item.setForeground(viewer.getControl().getDisplay()
//								.getSystemColor(SWT.DEFAULT));
//						return;
//					}
//				}
//			}
//			if (element instanceof FSTField) {
//				for (FSTField field : role.getFields()) {
//					if (field.comparesTo(element)) {
//						item.setForeground(viewer.getControl().getDisplay()
//								.getSystemColor(SWT.DEFAULT));
//						return;
//					}
//				}
//			}
//		}
		item.setForeground(viewer.getControl().getDisplay().getSystemColor(SWT.COLOR_GRAY));
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
				colorizeItems(viewer.getTree().getItems());
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

	@Override
	public void updateGuiAfterBuild(IFeatureProject project, IFile configurationFile) {
		if (iFile != null && project.equals(CorePlugin.getFeatureProject(iFile))) {
			IFile iFile2 = iFile;
			iFile = null;
			update(iFile2);
		}
	}
}