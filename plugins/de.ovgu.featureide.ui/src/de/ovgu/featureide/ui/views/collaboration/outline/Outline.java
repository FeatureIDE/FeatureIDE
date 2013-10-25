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
package de.ovgu.featureide.ui.views.collaboration.outline;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ISafeRunnable;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SafeRunner;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.core.runtime.content.IContentType;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuCreator;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.ITreeViewerListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeExpansionEvent;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Menu;
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
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.RoleElement;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.FmTreeContentProvider;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;

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
public class Outline extends ViewPart implements ICurrentBuildListener, IPropertyChangeListener {
	private static final String OUTLINE_ID = "de.ovgu.featureide.ui.views.outline";	 
	
	private static int selectedOutlineType;
	
	private ArrayList<IAction> actionOfProv = new ArrayList<IAction>();

	private void checkForExtensions() {
		IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(OUTLINE_ID);
		
		for (IConfigurationElement e : config) {
			try {
				final Object o = e.createExecutableExtension("contentProvider");
				final Object o2 = e.createExecutableExtension("labelProvider");
				if (o instanceof ITreeContentProvider && o2 instanceof OutlineLabelProvider) {
					executeExtension((ITreeContentProvider) o, (OutlineLabelProvider) o2);
				}
			} catch (CoreException ex) {
				UIPlugin.getDefault().logError(ex);
			}
		}
	}
	  
	private void executeExtension(final ITreeContentProvider contentProv, final OutlineLabelProvider labelProv) {
		ISafeRunnable runnable = new ISafeRunnable() {
			@Override
			public void handleException(Throwable e) {
				UIPlugin.getDefault().logError(e);
			}

			@Override
			public void run() throws Exception {
				addContentProv(contentProv, labelProv);
			}
		};
		SafeRunner.run(runnable);
	}
	  
	public void addContentProv(final ITreeContentProvider contentProv, final OutlineLabelProvider labelProv) {
		if (curContentProvider == null || curClabel == null) {
			curContentProvider = contentProv;
			curClabel = labelProv;
		}
		
		actionOfProv.add(new ProviderAction(labelProv.getLabelProvName(), labelProv.getOutlineType(), contentProv, labelProv) {
			public void run(){
				curContentProvider = this.getTreeContentProvider();
				curClabel = this.getLabelProvider();
				update(iFile);
			}
		});
		
	}
	
	private TreeViewer viewer;
	private IFile iFile;
	private IEditorPart active_editor;
	private UIJob uiJob;
	
	private ITreeContentProvider curContentProvider ;
	private OutlineLabelProvider curClabel = new CollaborationOutlineLabelProvider();
	
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
							UIPlugin.getDefault().logError(e);
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
	
	public Outline() {
		super();
		
		addContentProv(new ITreeContentProvider() {
			
			@Override
			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
				
			}
			
			@Override
			public void dispose() {
				
			}
			
			@Override
			public boolean hasChildren(Object element) {
				return false;
			}
			
			@Override
			public Object getParent(Object element) {
				return null;
			}
			
			@Override
			public Object[] getElements(Object inputElement) {
				return new String[] { "An outline is not available." };
			}
			
			@Override
			public Object[] getChildren(Object parentElement) {
				return null;
			}
		}, new OutlineLabelProvider(){

			@Override
			public Image getImage(Object element) {
				return null;
			}

			@Override
			public String getText(Object element) {
				return element.toString();
			}

			@Override
			public void addListener(ILabelProviderListener listener) {
				
			}

			@Override
			public void dispose() {
				
			}

			@Override
			public boolean isLabelProperty(Object element, String property) {
				return false;
			}

			@Override
			public void removeListener(ILabelProviderListener listener) {
				
			}

			@Override
			public int getOutlineType() {
				return OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
			}

			@Override
			public void colorizeItems(TreeItem[] treeItems) {
				
			}

			@Override
			public void setForeground(TreeItem item) {
				
			}

			@Override
			public String getLabelProvName() {
				return "Empty Outline";
			}
			
		});
		addContentProv(new CollaborationOutlineTreeContentProvider(), new CollaborationOutlineLabelProvider());
		addContentProv(new FmTreeContentProvider(), new FMOutlineLabelProviderWrapper());
	
		checkForExtensions();
		
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
//								update(file);
								if("model.xml".equals(file.getName())){
									selectedOutlineType = OutlineLabelProvider.OUTLINE_FEATURE_MODEL;
								}else if(file.getFileExtension().compareTo("java") == 0){
									selectedOutlineType = OutlineLabelProvider.OUTLINE_CODE;
								}else{
									selectedOutlineType = OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
								}
								iFile = file;
								fireSelectedAction();
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

	private IPropertyListener plistener = new IPropertyListener() {
		@Override
		public void propertyChanged(Object source, int propId) {
			update(iFile);
		}
	};
	

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
		
		fillLocalToolBar( getViewSite().getActionBars().getToolBarManager());
	}
	
	private Action dropDownAction = new Action("Outline Selection", Action.AS_DROP_DOWN_MENU) {
		{
			setImageDescriptor(ImageDescriptor
					.createFromImage(GUIDefaults.REFESH_TAB_IMAGE));
		}
	};
	
	/**
	 * @param toolBarManager
	 */
	private void fillLocalToolBar(IToolBarManager manager) {		
		dropDownAction.setMenuCreator(new IMenuCreator() {
			Menu fMenu = null;
			@Override
			public Menu getMenu(Menu parent) {
				return null;
			}
			
			@Override
			public Menu getMenu(Control parent) {
				fMenu = new Menu(parent);
				
				for (IAction curAction : actionOfProv) {
					curAction.addPropertyChangeListener(Outline.this);
					if(curAction instanceof ProviderAction && 
							((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType ){
						ActionContributionItem item = new ActionContributionItem(curAction);
						
						item.fill(fMenu, -1);
					}
				}
				return fMenu;
			}
			
			@Override
			public void dispose() {
				 if (fMenu != null) {
				      fMenu.dispose();
				 }
			}
		});
		manager.add(dropDownAction);
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
		if (viewer != null) {
			Control control = viewer.getControl();
			if (control != null && !control.isDisposed()) {
//				if (refreshContent(iFile2)) {
//					return;
//				}
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
											viewer.setContentProvider(curContentProvider);
											viewer.setLabelProvider(curClabel);
											viewer.setInput(((FeatureModelEditor) active_editor).getFeatureModel());
											
											//recreate the context menu in case we switched to another model
											if (contextMenu == null || contextMenu
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
											curClabel.setFile(iFile);
											viewer.setContentProvider(curContentProvider);
											viewer.setLabelProvider(curClabel);
											viewer.setInput(iFile);
										}
									} else {
										// simply remove the content from the outline
										//case: no providers set
										if (viewer.getContentProvider() == null) {
											viewer.setContentProvider(curContentProvider);
										}
										if (!(viewer.getLabelProvider() instanceof CollaborationOutlineLabelProvider)) {
											viewer.setLabelProvider(curClabel);
										}
										viewer.setInput(null);
									}
									colorizeItems(viewer.getTree().getItems());
									viewer.getControl().setEnabled(
													Outline.this.iFile != null);
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

//	/**
//	 * This method only updates the root and colors
//	 * @return <code>false</code> if the content needs to be replaced
//	 */
//	private boolean refreshContent(IFile iFile2) {
//		if (iFile2 != null && iFile != null) {
//			/** only set the colors of the tree if the content is the same **/
//			TreeItem[] items = viewer.getTree().getItems();
//			if (iFile2.getName().equals(iFile.getName()) && items.length > 0) {
//				TreeItem item = items[0];
//				if (item != null) {
//					if (item.getData() instanceof FSTClass) {
//						if (!hasSameClass((FSTClass) item.getData(), iFile2)) {
//							return false;
//						}
//						iFile = iFile2;
//						String toAppend = " - Composed class"; 
//						for (FSTRole r : ((FSTClass)item.getData()).getRoles()) {
//							if (!r.getDirectives().isEmpty()) {
//								toAppend =  "";
//								break;
//							}
//							if (r.getFile().equals(iFile)) {
//								toAppend = " - " + r.getFeature().getName();
//								break;
//							}
//						}
//						item.setText(((FSTClass)item.getData()).getName()+toAppend);
//						colorizeItems(viewer.getTree().getItems());
//						return true;
//					}
//				}
//			}
//		}
//		return false;
//	}
//
//	/**
//	 * @return <code>true</code> if the new input does not change the old content.
//	 */
//	private boolean hasSameClass(FSTClass Class, IFile iFile2) {
//		if (!iFile2.getProject().equals(iFile.getProject())) {
//			return false;
//		}
//		if (isBuildFile(iFile2.getParent(), 
//				CorePlugin.getFeatureProject(iFile2).getBuildFolder())) {
//			return true;
//		}
//		if (isBuildFile(iFile.getParent(), 
//				CorePlugin.getFeatureProject(iFile).getBuildFolder())) {
//			return true;
//		}
//		
//		if (iFile2.equals(iFile)) {
//			return true;
//		}
//		boolean i = false;
//		boolean j = false;
//		for (FSTRole role : Class.getRoles()) {
//			if (role.getFile().equals(iFile)) {
//				i = true;
//			} else if (role.getFile().equals(iFile2)) {
//				j = true;
//			}
//		}
//		return j && i;
//	}
//
//	/**
//	 * @param parent
//	 * @param buildFolder
//	 * @return <code>true</code> if the build folder contains the given folder
//	 */
//	private boolean isBuildFile(IContainer parent, IFolder buildFolder) {
//		if (parent == null) {
//			return false;
//		}
//		if (parent instanceof IFolder) {
//			if (parent.equals(buildFolder)) {
//				return true;
//			}
//			return isBuildFile(parent.getParent(), buildFolder);
//		}
//		return false;
//	}

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

	private void setForeground(TreeItem item) {
		RoleElement element = (RoleElement) item.getData();
		
		for (FSTRole role : element.getRole().getFSTClass().getRoles()) {
			if (!role.getFile().equals(iFile)) {
				continue;
			}
			if (element instanceof FSTMethod) {
				for (FSTMethod method : role.getMethods()) {
					if (method.comparesTo(element)) {
						item.setForeground(viewer.getControl().getDisplay()
								.getSystemColor(SWT.DEFAULT));
						return;
					}
				}
			}
			if (element instanceof FSTField) {
				for (FSTField field : role.getFields()) {
					if (field.comparesTo(element)) {
						item.setForeground(viewer.getControl().getDisplay()
								.getSystemColor(SWT.DEFAULT));
						return;
					}
				}
			}
		}
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

	@Override
	public void propertyChange(PropertyChangeEvent event) {
		if(event.getSource() instanceof ProviderAction && ((ProviderAction) event.getSource()).isChecked()){
			for (IAction curAction : actionOfProv) {
				if(curAction != event.getSource()){
					if(((ProviderAction) event.getSource()).getLabelProvider().getOutlineType() == ((ProviderAction) curAction).getLabelProvider().getOutlineType()){
						curAction.setChecked(false);
					}
				}
			}
		}
		
	}
	
	private void fireSelectedAction() {
		for (IAction curAction : actionOfProv) {
			if(((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType 
					&& curAction.isChecked()){
				curAction.run();
				return;
			}
		}
		for (IAction curAction : actionOfProv) {
			if(((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType){
				curAction.setChecked(true);
				curAction.run();
				return;
			}
		}
	}
}