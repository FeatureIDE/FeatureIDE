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
package de.ovgu.featureide.ui.views.collaboration.outline;

import static de.ovgu.featureide.fm.core.localization.StringTable.AN_OUTLINE_IS_NOT_AVAILABLE_;
import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.EMPTY_OUTLINE;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPAND_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDE_FIELDS;
import static de.ovgu.featureide.fm.core.localization.StringTable.HIDE_METHODS;
import static de.ovgu.featureide.fm.core.localization.StringTable.OUTLINE_SELECTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SORT_BY_FEATURE;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATE_OUTLINE_VIEW;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

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
import de.ovgu.featureide.core.builder.IComposerExtensionClass;
import de.ovgu.featureide.core.fstmodel.FSTClassFragment;
import de.ovgu.featureide.core.fstmodel.FSTField;
import de.ovgu.featureide.core.fstmodel.FSTInvariant;
import de.ovgu.featureide.core.fstmodel.FSTMethod;
import de.ovgu.featureide.core.fstmodel.FSTRole;
import de.ovgu.featureide.core.fstmodel.preprocessor.FSTDirective;
import de.ovgu.featureide.core.listeners.ICurrentBuildListener;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.FmTreeContentProvider;
import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.GUIDefaults;
import de.ovgu.featureide.ui.views.outline.ContextOutlineLabelProvider;
import de.ovgu.featureide.ui.views.outline.ContextOutlineTreeContentProvider;

/**
 * Another outline view displaying the same information as the collaboration
 * diagram
 * 
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Reimar Schroeter
 * @author Dominic Labsch
 * @author Daniel Psche
 */
/*
 * TODO #404 fix bug: do not close the tree if a corresponding file was opened
 * with an other way e.g. via collaboration diagram
 * 
 * TODO Sometimes the outline has no content -> display a warning / message
 */
public class Outline extends ViewPart implements ICurrentBuildListener, IPropertyChangeListener {
	private static final String OUTLINE_ID = "de.ovgu.featureide.ui.views.outline";

	private static int selectedOutlineType;

	private TreeViewer viewer;
	private IFile iFile;
	private IEditorPart active_editor;
	private UIJob uiJob;

	private ITreeContentProvider curContentProvider;
	private OutlineLabelProvider curClabel;

	private FmOutlinePageContextMenu contextMenu;

	private static final ImageDescriptor IMG_COLLAPSE = UIPlugin.getDefault().getImageDescriptor("icons/collapse.gif");
	private static final ImageDescriptor IMG_EXPAND = UIPlugin.getDefault().getImageDescriptor("icons/expand.gif");
	private static final ImageDescriptor IMG_SHOW_FIELDS = UIPlugin.getDefault().getImageDescriptor("icons/fields_co.gif");
	private static final ImageDescriptor IMG_SHOW_METHODS = UIPlugin.getDefault().getImageDescriptor("icons/methods_co.gif");
	private static final ImageDescriptor IMG_SORT_FEATURES = UIPlugin.getDefault().getImageDescriptor("icons/alphab_sort_co.gif");

	public static final String ID = UIPlugin.PLUGIN_ID + ".views.collaboration.outline.CollaborationOutline";

	private ArrayList<IAction> actionOfProv = new ArrayList<IAction>();
	private boolean providerChanged = false;

	private final SortByOccurrenceInFeature filter = new SortByOccurrenceInFeature();

	private static final Set<String> supportedTypes = new HashSet<>();
	static {
		supportedTypes.add("java");
		supportedTypes.add("jak");
		supportedTypes.add("hs");
		supportedTypes.add("h");
		supportedTypes.add("c");
		supportedTypes.add("cs");
		supportedTypes.add("asm");
	}

	private boolean hideAllFieldsToggle = false;
	private boolean hideAllMethodsToggle = false;
	private boolean sortFeatureToggle = false;

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
			if (viewer.getLabelProvider() instanceof OutlineLabelProvider) {
				((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), iFile);
			}
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
				//if a method or field is selected, the selection's FSTRole is always the first role of the first feature in the respective expandable
				//list in the outline no matter if the currently opened file contains the method.
				Object selection = ((IStructuredSelection) viewer.getSelection()).getFirstElement();
				FSTRole r = null;
				boolean fileAlreadyOpen = false;
				if (selection instanceof FSTRole) {
					r = (FSTRole) selection;
					selection = viewer.getTree().getSelection()[0].getParentItem().getData();
				} else if (selection instanceof FSTMethod) {
					FSTMethod meth = ((FSTMethod) selection);
					fileAlreadyOpen = meth.getFile().getName().equals(iFile.getName()) && (getMethodLine(iFile, meth) > 0);
					r = meth.getRole();
					if (meth.getLine() != -1)
						scrollToLine(active_editor, meth.getLine());
				} else if (selection instanceof FSTField) {
					FSTField field = ((FSTField) selection);
					fileAlreadyOpen = field.getFile().getName().equals(iFile.getName()) && (getFieldLine(iFile, field) > 0);
					r = field.getRole();
				} else if (selection instanceof FSTInvariant) {
					FSTInvariant invariant = ((FSTInvariant) selection);
					fileAlreadyOpen = invariant.getFile().getName().equals(iFile.getName()) && (getInvariantLine(iFile, invariant) > 0);
					r = invariant.getRole();
				} else if (selection instanceof FSTDirective) {
					fileAlreadyOpen = true;

				} else if (selection instanceof FSTClassFragment) {
					FSTClassFragment innerClass = ((FSTClassFragment) selection);
					fileAlreadyOpen = innerClass.getFile().getName().equals(iFile.getName()) && (getClassFragmentLine(iFile, innerClass) > 0);
					r = innerClass.getRole();
				}

				else {
					return;
				}
				if (!fileAlreadyOpen && r.getFile().isAccessible()) {
					IWorkbench workbench = PlatformUI.getWorkbench();
					IWorkbenchWindow window = workbench.getActiveWorkbenchWindow();
					IWorkbenchPage page = window.getActivePage();
					IContentType contentType = null;
					try {
						iFile = r.getFile();
						IContentDescription description = iFile.getContentDescription();
						if (description != null) {
							contentType = description.getContentType();
						}
						IEditorDescriptor desc = null;
						if (contentType != null) {
							desc = workbench.getEditorRegistry().getDefaultEditor(iFile.getName(), contentType);
						} else {
							desc = workbench.getEditorRegistry().getDefaultEditor(iFile.getName());
						}
						if (desc != null) {
							page.openEditor(new FileEditorInput(iFile), desc.getId());
						} else {
							// case: there is no default editor for the file
							page.openEditor(new FileEditorInput(iFile), "org.eclipse.ui.DefaultTextEditor");
						}

					} catch (CoreException e) {
						UIPlugin.getDefault().logError(e);
					}
				}

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
				} else if (selection instanceof FSTInvariant) {
					FSTInvariant inv = (FSTInvariant) selection;
					int line = getInvariantLine(iFile, inv);
					if (line != -1)
						scrollToLine(active_editor, line);

				} else if (selection instanceof FSTClassFragment) {
					FSTClassFragment cf = (FSTClassFragment) selection;
					int line = getClassFragmentLine(iFile, cf);
					if (line != -1)
						scrollToLine(active_editor, line);
				}

				else if (selection instanceof FSTDirective) {
					FSTDirective directive = (FSTDirective) selection;
					scrollToLine(active_editor, directive.getStartLine(), directive.getEndLine(), directive.getStartOffset(), directive.getEndLength());
				}
			}

		}

		// TODO refactor into FSTModel
		private int getFieldLine(IFile iFile, FSTField field) {
			for (FSTRole r : field.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTField f : r.getAllFields()) {
						if (f.compareTo(field) == 0) {
							return f.getLine();
						}
					}
				}
			}
			return -1;
		}

		private int getInvariantLine(IFile iFile, FSTInvariant inv) {
			for (FSTRole r : inv.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTInvariant i : r.getClassFragment().getInvariants()) {
						if (i.compareTo(inv) == 0) {
							return i.getLine();
						}
					}
				}
			}
			return -1;
		}

		private int getClassFragmentLine(IFile iFile, FSTClassFragment cf) {
			for (FSTRole r : cf.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTClassFragment i : r.getAllInnerClasses()) {
						if (i.compareTo(cf) == 0) {
							return i.getLine();
						}
					}
				}
			}
			return -1;
		}

		private int getMethodLine(IFile iFile, FSTMethod meth) {
			for (FSTRole r : meth.getRole().getFSTClass().getRoles()) {
				if (r.getFile().equals(iFile)) {
					for (FSTMethod m : r.getAllMethods()) {
						if (m.compareTo(meth) == 0) {
							return m.getLine();
						}
					}
				}
			}
			return -1;
		}

	};

	private void checkForExtensions() {
		IConfigurationElement[] config = Platform.getExtensionRegistry().getConfigurationElementsFor(OUTLINE_ID);

		for (IConfigurationElement e : config) {
			try {
				final Object contentProvider = e.createExecutableExtension("contentProvider");
				final Object labelProvider = e.createExecutableExtension("labelProvider");
				if (contentProvider instanceof ITreeContentProvider && labelProvider instanceof OutlineLabelProvider) {
					executeExtension((ITreeContentProvider) contentProvider, (OutlineLabelProvider) labelProvider);
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
		curContentProvider = contentProv;
		curClabel = labelProv;
		labelProv.initTreeViewer(Outline.this.viewer);

		ProviderAction provAct = new ProviderAction(labelProv.getLabelProvName(), labelProv.getOutlineType(), contentProv, labelProv) {
			public void run() {
				if (curContentProvider != this.getTreeContentProvider() || curClabel != this.getLabelProvider()) {
					curContentProvider = this.getTreeContentProvider();
					curClabel = this.getLabelProvider();
					providerChanged = true;
					update(iFile);
				}
			}
		};
		actionOfProv.add(provAct);
	}

	private Action dropDownAction = new Action(OUTLINE_SELECTION, Action.AS_DROP_DOWN_MENU) {
		{
			setImageDescriptor(ImageDescriptor.createFromImage(GUIDefaults.REFESH_TAB_IMAGE));
		}
	};

	public Outline() {
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

						// case: open editor
						FileEditorInput inputFile = (FileEditorInput) part.getEditorInput();
						IFile file = inputFile.getFile();

						IFeatureProject featureProject = CorePlugin.getFeatureProject(file);

						if (featureProject != null) {
							Control control = viewer.getControl();
							if (control != null && !control.isDisposed()) {
								final String extension = file.getFileExtension();

								if ("xml".equalsIgnoreCase(extension)) {
									selectedOutlineType = OutlineLabelProvider.OUTLINE_FEATURE_MODEL;
								} else if (supportedTypes.contains(extension)) {
									selectedOutlineType = OutlineLabelProvider.OUTLINE_CODE;
								} else {
									selectedOutlineType = OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
								}
								fireSelectedAction();

								update(file);
							}
						} else {
							selectedOutlineType = OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
							fireSelectedAction();
							update(null);
						}
						active_editor.addPropertyListener(plistener);
						return;
					}
				}
			}
		}
		// remove content from TreeViewer
		selectedOutlineType = OutlineLabelProvider.OUTLINE_NOT_AVAILABLE;
		fireSelectedAction();
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

		addContentProv(new NotAvailableContentProv(), new NotAvailableLabelProv());
		addContentProv(new CollaborationOutlineTreeContentProvider(), new CollaborationOutlineLabelProvider());
		addContentProv(new FmTreeContentProvider(), new FMOutlineLabelProviderWrapper());
		addContentProv(new ContextOutlineTreeContentProvider(), new ContextOutlineLabelProvider());
		
		addContentProv(new MungeExtendedContentProvider(), new MungeOutlineLabelProvider());

		checkForExtensions();

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

		fillLocalToolBar(getViewSite().getActionBars().getToolBarManager());
	}

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
					if (curAction instanceof ProviderAction && ((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType) {
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
				if (filter.isEnabled()) {
					filter.setFile(iFile2);
				}
				if (providerChanged || !refreshContent(iFile, iFile2) || filter.isEnabled()) {
					providerChanged = false;

					iFile = iFile2;

					if (uiJob == null || uiJob.getState() == Job.NONE) {
						uiJob = new UIJob(UPDATE_OUTLINE_VIEW) {
							public IStatus runInUIThread(IProgressMonitor monitor) {

								if (viewer != null) {
									if (viewer.getControl() != null && !viewer.getControl().isDisposed()) {
										viewer.getControl().setRedraw(false);

										viewer.setContentProvider(curContentProvider);
										viewer.setLabelProvider(curClabel);
										if (iFile != null) {
											if ("xml".equalsIgnoreCase(iFile.getFileExtension()) && active_editor instanceof FeatureModelEditor) {
												viewer.setInput(((FeatureModelEditor) active_editor).getFeatureModel());

												// recreate the context menu in case
												// we switched to another model
												if (contextMenu == null
														|| contextMenu.getFeatureModel() != ((FeatureModelEditor) active_editor).getFeatureModel()) {
													if (contextMenu != null) {
														// the listener isn't
														// recreated, if it still
														// exists
														// but we need a new
														// listener for the new
														// model
														viewer.removeDoubleClickListener(contextMenu.dblClickListener);
													}
													contextMenu = new FmOutlinePageContextMenu(getSite(), (FeatureModelEditor) active_editor, viewer,
															((FeatureModelEditor) active_editor).getFeatureModel());
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
								return Status.OK_STATUS;
							}
						};
						uiJob.setPriority(Job.SHORT);
						uiJob.schedule();
					}
				}
			}
		}
	}
	
	private boolean refreshContent(IFile oldFile, IFile currentFile) {
		sortMethods.setEnabled(false);
		hideAllFields.setEnabled(false);
		hideAllMethods.setEnabled(false);
		if (currentFile != null) {
			final IFeatureProject featureProject = CorePlugin.getFeatureProject(currentFile);
			if (featureProject != null) {
				final IComposerExtensionClass composer = featureProject.getComposer();
				if (composer != null) {
					if (composer.showContextFieldsAndMethods()) {
						sortMethods.setEnabled(true);
						hideAllFields.setEnabled(true);
						hideAllMethods.setEnabled(true);
					}
					if (viewer.getLabelProvider() instanceof OutlineLabelProvider) {
						OutlineLabelProvider lp = (OutlineLabelProvider) viewer.getLabelProvider();
						return lp.refreshContent(oldFile, currentFile);
					}
				}
			}
		} 
		return false;
	}

	// create Action to hide all fields
	private final Action hideAllFields = new Action("", Action.AS_CHECK_BOX) {
		private HideAllFields filter = new HideAllFields();

		public void run() {
			hideAllFieldsToggle = !hideAllFieldsToggle;

			if (viewer.getContentProvider() instanceof CollaborationOutlineTreeContentProvider) {
				CollaborationOutlineTreeContentProvider contentProvider = (CollaborationOutlineTreeContentProvider) viewer.getContentProvider();
				CollaborationOutlineLabelProvider labelProvider = (CollaborationOutlineLabelProvider) viewer.getLabelProvider();
				if (hideAllFieldsToggle) {
					contentProvider.addFilter(filter);
				} else {
					contentProvider.removeFilter(filter);
				}
				viewer.refresh();
				labelProvider.refreshContent(iFile, (IFile) viewer.getInput());
			}
		}
	};

	// create Action to hide all methods
	private final Action hideAllMethods = new Action("", Action.AS_CHECK_BOX) {
		private HideAllMethods filter = new HideAllMethods();

		public void run() {
			hideAllMethodsToggle = !hideAllMethodsToggle;

			if (viewer.getContentProvider() instanceof CollaborationOutlineTreeContentProvider) {
				CollaborationOutlineTreeContentProvider contentProvider = (CollaborationOutlineTreeContentProvider) viewer.getContentProvider();
				CollaborationOutlineLabelProvider labelProvider = (CollaborationOutlineLabelProvider) viewer.getLabelProvider();
				if (hideAllMethodsToggle) {
					contentProvider.addFilter(filter);
				} else {
					contentProvider.removeFilter(filter);
				}
				viewer.refresh();
				labelProvider.refreshContent(iFile, (IFile) viewer.getInput());
			}
		}
	};

	// create Action to display methods and fields in the current feature on top
	private final Action sortMethods = new Action("", Action.AS_CHECK_BOX) {

		public void run() {
			sortFeatureToggle = !sortFeatureToggle;
			if (viewer.getContentProvider() instanceof CollaborationOutlineTreeContentProvider) {
				CollaborationOutlineTreeContentProvider contentProvider = (CollaborationOutlineTreeContentProvider) viewer.getContentProvider();
				CollaborationOutlineLabelProvider labelProvider = (CollaborationOutlineLabelProvider) viewer.getLabelProvider();
				if (sortFeatureToggle) {
					if (viewer.getInput() instanceof IFile) {
						filter.setFile(iFile);
						filter.setEnabled(true);
						contentProvider.addFilter(filter);
						viewer.refresh();
						labelProvider.refreshContent(iFile, (IFile) viewer.getInput());
					}
				} else {
					if (filter != null) {
						filter.setEnabled(false);
						contentProvider.removeFilter(filter);
						viewer.refresh();
						labelProvider.refreshContent(iFile, (IFile) viewer.getInput());
					}
				}
			}
		}
	};

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
				if (viewer.getLabelProvider() instanceof OutlineLabelProvider) {
					((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), iFile);
				}
			}
		};
		collapseAllAction.setToolTipText(COLLAPSE_ALL);
		collapseAllAction.setImageDescriptor(IMG_COLLAPSE);

		Action expandAllAction = new Action() {
			public void run() {
				viewer.expandAll();
				// treeExpanded event is not triggered, so we manually have to
				// call this function
				if (viewer.getLabelProvider() instanceof OutlineLabelProvider) {
					((OutlineLabelProvider) viewer.getLabelProvider()).colorizeItems(viewer.getTree().getItems(), iFile);
				}
			}
		};

		expandAllAction.setToolTipText(EXPAND_ALL);
		expandAllAction.setImageDescriptor(IMG_EXPAND);
		hideAllFields.setToolTipText(HIDE_FIELDS);
		hideAllFields.setImageDescriptor(IMG_SHOW_FIELDS);
		hideAllMethods.setToolTipText(HIDE_METHODS);
		hideAllMethods.setImageDescriptor(IMG_SHOW_METHODS);
		sortMethods.setToolTipText(SORT_BY_FEATURE);
		sortMethods.setImageDescriptor(IMG_SORT_FEATURES);

		iToolBarManager.add(collapseAllAction);
		iToolBarManager.add(expandAllAction);
		iToolBarManager.add(hideAllFields);
		iToolBarManager.add(hideAllMethods);
		iToolBarManager.add(sortMethods);
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
		IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
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
	 * @param startLine
	 *            the first line of a directive
	 * @param endLine
	 *            the last line of a directive
	 * @param startOffset
	 *            characters before the statement starts
	 * @param endOffset
	 *            length of the last line
	 */
	public static void scrollToLine(IEditorPart editorPart, int startLine, int endLine, int startOffset, int endOffset) {
		if (!(editorPart instanceof ITextEditor) || startLine < 0 || endLine < 0) {
			return;
		}
		ITextEditor editor = (ITextEditor) editorPart;
		IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
		if (document != null) {
			try {
				int offset = document.getLineOffset(startLine) + startOffset;
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
		if (event.getSource() instanceof ProviderAction && ((ProviderAction) event.getSource()).isChecked()) {
			for (IAction curAction : actionOfProv) {
				if (curAction != event.getSource()) {
					if (((ProviderAction) event.getSource()).getLabelProvider().getOutlineType() == ((ProviderAction) curAction).getLabelProvider()
							.getOutlineType()) {
						curAction.setChecked(false);
					}
				}
			}
			update(iFile);
		}

	}

	private void fireSelectedAction() {
		for (IAction curAction : actionOfProv) {
			if (((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType && curAction.isChecked()) {
				curAction.run();
				return;
			}
		}
		for (IAction curAction : actionOfProv) {
			if (((ProviderAction) curAction).getLabelProvider().getOutlineType() == selectedOutlineType) {
				curAction.setChecked(true);
				curAction.run();
				return;
			}
		}
	}

	private class NotAvailableLabelProv extends OutlineLabelProvider {

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
		public void colorizeItems(TreeItem[] treeItems, IFile file) {
		}

		@Override
		public void setForeground(TreeItem item, IFile file) {
		}

		@Override
		public String getLabelProvName() {
			return EMPTY_OUTLINE;
		}

		@Override
		public boolean refreshContent(IFile oldFile, IFile currentFile) {
			return false;
		}

		/*
		 * (non-Javadoc)
		 * 
		 * @see
		 * de.ovgu.featureide.ui.views.collaboration.outline.OutlineLabelProvider
		 * #init()
		 */
		@Override
		public void init() {

		}

	}

	private class NotAvailableContentProv implements ITreeContentProvider {

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

		// TODO
		public Object[] getElements(Object inputElement) {
			// if (inputElement == null || !(inputElement instanceof IFile))
			// return new String[] { NO_FILE_FOUND };

			// IFeatureProject featureProject = CorePlugin
			// .getFeatureProject((IFile) inputElement);
			// if (featureProject != null) {
			// if (model != null) {
			// FSTClass c = model.getClass(((IFile) inputElement).getName());
			// if (c != null) {
			// return new Object[] { c };
			// } else {
			return new String[] { AN_OUTLINE_IS_NOT_AVAILABLE_ };
			// }
			// } else {
			// return new String[] { "Collaboration Model not found" };
			// }
			// } else {
			// return new String[] { THIS_IS_NO_FEATURE_PROJECT };
			// }
		}

		// @Override
		// public Object[] getElements(Object inputElement) {
		// return new String[] { AN_OUTLINE_IS_NOT_AVAILABLE_ };
		// }

		@Override
		public Object[] getChildren(Object parentElement) {
			return null;
		}
	}
}
