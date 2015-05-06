/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2015  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.examples.wizards;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerComparator;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.examples.utils.CommentParser;
import de.ovgu.featureide.examples.utils.ExampleStructureProvider;
import de.ovgu.featureide.examples.utils.ZipStructureProvider;

/**
 * This class represents one page of the Example Wizard.
 * 
 * @author Christian Becker
 */
public class ExampleNewWizardPage extends WizardPage implements IOverwriteQuery {

	private static final class ExampleLabelProvider extends LabelProvider {
		public String getText(Object element) {
			if (element instanceof String) {
				for (IComposerExtensionBase ic : ComposerExtensionManager.getInstance().getComposers()) {
					final String composerExtension = ic.toString();
					if (composerExtension.substring(composerExtension.lastIndexOf(".") + 1).equals((String) element)) {
						return ic.getName();
					}
				}
				return (String) element;
			} else if (element instanceof ProjectRecord) {
				return ((ProjectRecord) element).getProjectLabel();
			} else {
				return "";
			}
		}
	}

	private static class ItemAccessCheckboxTreeViewer extends CheckboxTreeViewer {

		/**
		 * @param parent
		 * @param style
		 */
		public ItemAccessCheckboxTreeViewer(Composite parent, int style) {
			super(parent, style);
		}

		public TreeItem findTreeItem(Object element) {
			Widget widget = findItem(element);
			if (widget instanceof TreeItem) {
				return (TreeItem) widget;
			}
			return null;
		}

		public void refresh() {
			// Save selected and expanded elements;
			final Set<Object> checkedElements = new HashSet<>(Arrays.asList(getCheckedElements()));
			final Set<Object> expandedElements = new HashSet<>(Arrays.asList(getExpandedElements()));
			
			getTree().setRedraw(false);

			//update tree and load all elements regarding the filter
			super.refresh();
			expandAll();
			collapseAll();

			//reset all selected and expanded elements
			for (TreeItem parentItems : getTree().getItems()) {
				if (parentItems.getData() instanceof String) {
					if (expandedElements.contains(parentItems.getData())) {
						parentItems.setExpanded(true);
					}
					for (TreeItem currItem : parentItems.getItems()) {
						if (currItem.getData() instanceof ProjectRecord) {
							ProjectRecord tmpRecord = (ProjectRecord) currItem.getData();
							if (tmpRecord.hasErrors()) {
								currItem.setForeground(red);
							} else if (tmpRecord.hasWarnings()) {
								currItem.setForeground(gray);
							} else {
								currItem.setForeground(black);
							}
							if (checkedElements.contains(tmpRecord)) {
								currItem.setChecked(true);
							}
						}
					}
				}
			}
			getTree().setRedraw(true);		
		}

	}

	private class ExampleProjectFilter extends ViewerFilter {

		private String searchText = null;

		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			if (searchText == null || searchText.isEmpty() || FILTERTEXT.equals(searchFeatureText.getText())) {
				return true;
			} else if (element instanceof String) {
				for (ProjectRecord tmpRecord : compTable.get(element)) {
					if (tmpRecord.getProjectName().toLowerCase(Locale.ENGLISH).contains(searchText)) {
						return true;
					}
				}
				return false;
			} else if (element instanceof ProjectRecord) {
				return ((ProjectRecord) element).getProjectName().toLowerCase(Locale.ENGLISH).contains(searchText);
			} else {
				return false;
			}
		}

	}

	protected static final Color gray = new Color(null, 140, 140, 140);
	protected static final Color red = new Color(null, 240, 0, 0);
	protected static final Color black = new Color(null, 0, 0, 0);

	/**
	 * The name of the folder containing metadata information for the workspace.
	 */
	public static final String METADATA_FOLDER = ".metadata"; //$NON-NLS-1$

	/**
	 * The import structure provider.
	 * 
	 * @since 3.4
	 */
	private ZipStructureProvider structureProvider;

	private ItemAccessCheckboxTreeViewer projectsList;
	private Text descBox;

	private Hashtable<String, List<ProjectRecord>> compTable;
	private String samplePath;

	private static final String[] response = new String[] { YES, ALL, NO, NO_ALL, CANCEL };
	private static final String FILTERTEXT = "type filter text";

	private StyledText searchFeatureText;
	private final ExampleProjectFilter searchFilter = new ExampleProjectFilter();

	private static final String CHILD_WARNING = "Selected only fully compatible projects. "
			+ "(Manual selection for projects with warnings is still possible).";

	private Thread updateProjects;

	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 */
	public ExampleNewWizardPage(String samplePath) {
		super("Select FeatureIDE Example(s)");
		setTitle("Select FeatureIDE example(s) which you would like to explore");
		this.samplePath = samplePath;
	}

	public void createControl(Composite parent) {
		initializeDialogUnits(parent);

		Composite workArea = new Composite(parent, SWT.NONE);
		setControl(workArea);
		
		Label title = new Label(workArea, SWT.NONE);
		title.setText("Choosable Examples:");

		searchFeatureText = new StyledText(workArea, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		searchFeatureText.setText(FILTERTEXT);

		createProjectsList(workArea);

		createDescriptionArea(workArea);

		projectsList.addFilter(searchFilter);

		searchFeatureText.setForeground(gray);
		searchFeatureText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		searchFeatureText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				searchFilter.searchText = searchFeatureText.getText().toLowerCase(Locale.ENGLISH);
				projectsList.refresh();
			}

		});

		searchFeatureText.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (searchFeatureText.getText().isEmpty()) {
					searchFeatureText.setText(FILTERTEXT);
					searchFeatureText.setForeground(gray);
				}

			}
		});
		searchFeatureText.addListener(SWT.FocusIn, new Listener() {

			@Override
			public void handleEvent(Event event) {
				setMessage("");

				if (FILTERTEXT.equals(searchFeatureText.getText())) {
					searchFeatureText.setText("");
				}
				searchFeatureText.setForeground(black);
			}

		});

		workArea.setLayout(new GridLayout());
		workArea.setLayoutData(new GridData(GridData.FILL_BOTH | GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL));

		Dialog.applyDialogFont(workArea);
	}

	/**
	 * Create the checkbox list for the found projects.
	 * 
	 * @param workArea
	 */
	private void createProjectsList(final Composite workArea) {
		Composite listComposite = new Composite(workArea, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.numColumns = 2;
		layout.marginWidth = 0;
		layout.makeColumnsEqualWidth = false;
		listComposite.setLayout(layout);

		listComposite.setLayoutData(new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.FILL_BOTH));

		projectsList = new ItemAccessCheckboxTreeViewer(listComposite, SWT.BORDER);
		GridData listData = new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.FILL_BOTH);
		listData.minimumHeight = 175;
		projectsList.getControl().setLayoutData(listData);
		projectsList.setContentProvider(new ITreeContentProvider() {

			private ExampleNewWizardPage exampleNewWizardPage;

			@SuppressWarnings("unchecked")
			public Object[] getChildren(Object parentElement) {
				if (parentElement instanceof Hashtable) {
					return ((Hashtable<String, List<ProjectRecord>>) parentElement).keySet().toArray();
				} else if (parentElement instanceof String) {
					return compTable.get((String) parentElement).toArray();
				} else {
					return new Object[] { "Children could not be loaded." };
				}
			}

			public Object[] getElements(Object inputElement) {
				if (inputElement == null) {
					return new String[] { "Loading..." };
				} else if (inputElement == exampleNewWizardPage) {
					updateProjectsList(samplePath);
					if (updateProjects != null) {
						try {
							updateProjects.join();
						} catch (InterruptedException e) {
							ExamplePlugin.getDefault().logError(e);
						}
						return compTable.keySet().toArray();
					} else {
						return new Object[] { "Examples could not be loaded." };
					}
				} else {
					return getChildren(exampleNewWizardPage);
				}
			}

			public boolean hasChildren(Object element) {
				if (element instanceof Hashtable) {
					@SuppressWarnings("unchecked")
					Hashtable<String, List<ProjectRecord>> hashtable = (Hashtable<String, List<ProjectRecord>>) element;
					return hashtable.keySet().size() > 0;
				} else if (element instanceof String) {
					return compTable.containsKey((String) element) && !compTable.get((String) element).isEmpty();
				} else {
					return false;
				}
			}

			public Object getParent(Object element) {
				return null;
			}

			public void dispose() {
			}

			public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
				exampleNewWizardPage = (ExampleNewWizardPage) newInput;
			}
		});

		projectsList.setLabelProvider(new ExampleLabelProvider());

		projectsList.addCheckStateListener(new ICheckStateListener() {
			public void checkStateChanged(CheckStateChangedEvent event) {
				if (event.getElement() instanceof String) {
					for (ProjectRecord tmpRecord : compTable.get((String) event.getElement())) {
						final boolean isChecked = projectsList.getChecked((String) event.getElement());

						if (isChecked == false) {
							projectsList.setChecked(tmpRecord, isChecked);
						} else {
							if (tmpRecord.hasErrors() || tmpRecord.hasWarnings()) {
								projectsList.setChecked(tmpRecord, false);
								setMessage(CHILD_WARNING, INFORMATION);
							} else {
								projectsList.setChecked(tmpRecord, true);
							}
						}
					}
				} else if (event.getElement() instanceof ProjectRecord) {
					ProjectRecord tmpRecord = (ProjectRecord) event.getElement();
					if (tmpRecord.hasErrors()) {
						projectsList.setChecked(tmpRecord, false);
					}
					if (projectsList.getChecked(event.getElement())) {
						projectsList.findTreeItem(event.getElement()).getParentItem().setChecked(true);
					}
				}

				projectsList.setSelection(new StructuredSelection(event.getElement()));

				determineAndSetPageComplete();
			}
		});

		projectsList.addSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				if (event.getSelection() instanceof IStructuredSelection) {
					IStructuredSelection iss = (IStructuredSelection) event.getSelection();
					if (iss != null) {
						if (iss.getFirstElement() instanceof String) {
							descBox.setText("");
							setMessage("");

							TreeItem treeItem = projectsList.findTreeItem(iss.getFirstElement());
							boolean allProjectsSelected = true;
							for (TreeItem currItem : treeItem.getItems()) {
								if (currItem.getData() instanceof ProjectRecord) {
									ProjectRecord project = ((ProjectRecord) currItem.getData());
									if (currItem.getChecked() && project.hasWarnings()) {
										setMessage("Projects with warnings are selected.", WARNING);
										allProjectsSelected = true;
										break;
									}
									if (!currItem.getChecked() && !project.hasErrors()) {
										allProjectsSelected = false;
									}
								}
							}
							if (!allProjectsSelected && treeItem.getChecked()) {
								setMessage("Not all project selected.", INFORMATION);
							}
						} else if (iss.getFirstElement() instanceof ProjectRecord) {
							ProjectRecord tmpRecord = (ProjectRecord) iss.getFirstElement();
							if (tmpRecord != null) {
								descBox.setText(tmpRecord.getDescription());
								if (tmpRecord.hasErrors()) {
									setMessage(tmpRecord.getErrorText(), ERROR);
								} else if (tmpRecord.hasWarnings()) {
									setMessage(tmpRecord.getWarningText(), WARNING);
								} else {
									setMessage("");
								}
							}
						}
					}
				}
			}
		});

		projectsList.setInput(this);
		projectsList.setComparator(new ViewerComparator());

		createSelectionButtons(listComposite);

		// Children in CheckboxTreeViewer are only requested when explicitly
		// needed. When checking the composer checkbox
		// (parent) before once having expanded it, projects (children) had
		// actually not been checked when expanded
		// later. Hence projectsList gets expanded and collapsed completely in
		// the beginning to have all children/projects added.
		projectsList.expandAll();
		projectsList.collapseAll();
		setPageComplete(false);
	}

	private void createDescriptionArea(Composite workArea) {
		Label title = new Label(workArea, SWT.NONE);
		title.setText("Description:");

		descBox = new Text(workArea, SWT.BORDER | SWT.MULTI | SWT.WRAP | SWT.READ_ONLY | SWT.V_SCROLL);
		descBox.setText("");

		GridData dbDG = new GridData(GridData.FILL_BOTH);
		dbDG.minimumHeight = 75;
		descBox.setLayoutData(dbDG);

	}

	private void determineAndSetPageComplete() {
		for (Object obj : projectsList.getCheckedElements()) {
			if (obj instanceof ProjectRecord) {
				setPageComplete(true);
				break;
			}
			setPageComplete(false);
		}
	}

	/**
	 * Create the selection buttons in the listComposite.
	 * 
	 * @param listComposite
	 */
	private void createSelectionButtons(Composite listComposite) {
		Composite buttonsComposite = new Composite(listComposite, SWT.NONE);
		GridLayout layout = new GridLayout();
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		buttonsComposite.setLayout(layout);

		buttonsComposite.setLayoutData(new GridData(GridData.VERTICAL_ALIGN_BEGINNING));

		Button selectAll = new Button(buttonsComposite, SWT.PUSH);
		selectAll.setText("Select All");
		selectAll.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {

				selectAllElementsWithoutWarningsOrErrors();
				setPageComplete(projectsList.getCheckedElements().length > 0);
			}
		});
		Dialog.applyDialogFont(selectAll);
		setButtonLayoutData(selectAll);

		Button deselectAll = new Button(buttonsComposite, SWT.PUSH);
		deselectAll.setText("Deselect All");
		deselectAll.addSelectionListener(new SelectionAdapter() {
			public void widgetSelected(SelectionEvent e) {
				projectsList.setCheckedElements(new Object[0]);
				setMessage("");
				setPageComplete(false);
			}
		});
		Dialog.applyDialogFont(deselectAll);
		setButtonLayoutData(deselectAll);
	}

	/**
	 * Update the list of projects based on path. Method declared public only
	 * for test suite.
	 * 
	 * @param path
	 */
	public void updateProjectsList(final String path) {
		if (path == null || path.length() == 0) {
			setMessage("Select a directory to search for existing Eclipse projects.");
			projectsList.refresh(true);
			setPageComplete(projectsList.getCheckedElements().length > 0);
			return;
		}

		final File directory = new File(path);

		updateProjects = new Thread(new Runnable() {
			public void run() {

				NullProgressMonitor monitor = new NullProgressMonitor();
				monitor.beginTask("Searching for projects", 100);
				Collection<ProjectRecord> files = new ArrayList<ProjectRecord>();
				monitor.worked(10);

				if (isZipFile(path)) {
					ZipFile sourceFile = getSpecifiedZipSourceFile(path);
					if (sourceFile == null) {
						return;
					}
					structureProvider = new ZipStructureProvider(sourceFile);
					Object child = structureProvider.getRoot();

					if (!collectProjectFilesFromProvider(files, child, 0, monitor)) {
						return;
					}
					Iterator<ProjectRecord> filesIterator = files.iterator();
					monitor.worked(50);
					monitor.subTask("Processing results");
					compTable = new Hashtable<String, List<ProjectRecord>>();
					// FH, DeltaJ, AHEAD, Antenna, AspectJ, Colligens, FC++,
					// Munge

					while (filesIterator.hasNext()) {
						ProjectRecord pr = filesIterator.next();
						String compID = "", composer = "";

						for (ICommand command : pr.projectDescription.getBuildSpec()) {
							if (command.getArguments().containsKey("composer")) {
								compID = command.getArguments().get("composer");
								composer = compID.substring(compID.lastIndexOf(".") + 1);
								if (!compTable.containsKey(composer)) {
									compTable.put(composer, new ArrayList<ProjectRecord>());
								}
								compTable.get(composer).add(pr);
								break;
							}
						}
					}
				} else if (directory.isDirectory()) {
					if (!collectProjectFilesFromDirectory(files, directory, null, monitor)) {
						return;
					}
					Iterator<ProjectRecord> filesIterator = files.iterator();
					monitor.worked(50);
					monitor.subTask("Processing results");
					compTable = new Hashtable<String, List<ProjectRecord>>();
					// FH, DeltaJ, AHEAD, Antenna, AspectJ, Colligens, FC++,
					// Munge

					while (filesIterator.hasNext()) {
						ProjectRecord pr = filesIterator.next();
						String compID = "", composer = "";

						for (ICommand command : pr.projectDescription.getBuildSpec()) {
							if (command.getArguments().containsKey("composer")) {
								compID = command.getArguments().get("composer");
								composer = compID.substring(compID.lastIndexOf(".") + 1);
								System.out.println("command.getArgu: "+command.getArguments()+" compID: "+compID+" pr.projectDescri: "+pr.projectName);
								if (!compTable.containsKey(composer)) {
									compTable.put(composer, new LinkedList<ProjectRecord>());
								}
								compTable.get(composer).add(pr);
								break;
							}
						}
					}
				} else {
					monitor.worked(60);
				}
				monitor.done();
			}

		});
		updateProjects.start();
		if (projectsList != null) {
			projectsList.refresh(false);
		}
	}

	private void selectAllElementsWithoutWarningsOrErrors() {
		boolean errorOrWarningExist = false;

		TreeItem[] parentItems = projectsList.getTree().getItems();
		for (TreeItem currPItem : parentItems) {
			if (currPItem.getData() instanceof String) {
				currPItem.setChecked(true);
			}
			for (TreeItem currItem : currPItem.getItems()) {
				if (currItem.getData() instanceof ProjectRecord) {
					ProjectRecord projectRecord = (ProjectRecord) currItem.getData();
					if (projectRecord.hasErrors()) {
						currItem.setGrayed(true);
						errorOrWarningExist = true;
					} else if (projectRecord.hasWarnings()) {
						errorOrWarningExist = true;
					} else {
						currItem.setChecked(true);
						projectsList.setChecked(projectRecord, true);
					}
				}
			}
		}

		if (errorOrWarningExist) {
			setMessage(CHILD_WARNING, INFORMATION);
		}
	}

	/**
	 * Answer a handle to the zip file currently specified as being the source.
	 * Return null if this file does not exist or is not of valid format.
	 */
	private ZipFile getSpecifiedZipSourceFile(String fileName) {
		if (fileName.length() == 0) {
			return null;
		}

		try {
			return new ZipFile(fileName);
		} catch (ZipException e) {
			ExamplePlugin.getDefault().logError("Source file is not a valid Zip file.", e);

		} catch (IOException e) {
			ExamplePlugin.getDefault().logError("Source file could not be read.", e);
		}

		return null;
	}

	/**
	 * Collect the list of .project files that are under directory into files.
	 * 
	 * @param files
	 * @param monitor
	 *            The monitor to report to
	 * @return boolean <code>true</code> if the operation was completed.
	 */
	private boolean collectProjectFilesFromProvider(Collection<ProjectRecord> files, Object entry, int level, IProgressMonitor monitor) {

		if (monitor.isCanceled()) {
			return false;
		}
		monitor.subTask("Checking: " + structureProvider.getLabel(entry));
		List<ZipEntry> children = structureProvider.getChildren(entry);
		if (children == null) {
			children = new ArrayList<ZipEntry>(1);
		}
		Iterator<ZipEntry> childrenEnum = children.iterator();
		while (childrenEnum.hasNext()) {
			Object child = childrenEnum.next();
			if (structureProvider.isFolder(child)) {
				collectProjectFilesFromProvider(files, child, level + 1, monitor);
			}
			String elementLabel = structureProvider.getLabel(child);
			if (elementLabel.equals(IProjectDescription.DESCRIPTION_FILE_NAME)) {
				files.add(new ProjectRecord(child, entry, level));
			}
		}
		return true;
	}

	/**
	 * Collect the list of .project files that are under directory into files.
	 * 
	 * @param files
	 * @param directory
	 * @param directoriesVisited
	 *            Set of canonical paths of directories, used as recursion guard
	 * @param monitor
	 *            The monitor to report to
	 * @return boolean <code>true</code> if the operation was completed.
	 */
	private boolean collectProjectFilesFromDirectory(Collection<ProjectRecord> files, File directory, Set<String> directoriesVisited, IProgressMonitor monitor) {
		if (monitor.isCanceled()) {
			return false;
		}
		monitor.subTask("Checking: " + directory.getPath());
		File[] contents = directory.listFiles();
		if (contents == null)
			return false;

		// Initialize recursion guard for recursive symbolic links
		if (directoriesVisited == null) {
			directoriesVisited = new HashSet<String>();
			try {
				directoriesVisited.add(directory.getCanonicalPath());
			} catch (IOException exception) {
				exception.printStackTrace();
			}
		}

		// first look for project description files
		for (int i = 0; i < contents.length; i++) {
			final File file = contents[i];
			if (file.isFile() && IProjectDescription.DESCRIPTION_FILE_NAME.equals(file.getName())) {
				final ProjectRecord newProject = new ProjectRecord(file);
				files.add(newProject);
				if (newProject.containsNatureID("de.ovgu.featureide.core.mpl.MSPLNature")) {
					if (file.getParentFile().isDirectory()) {
						final File[] subdir = file.getParentFile().listFiles();
						if (subdir != null) {
							for (File file2 : subdir) {
								if (ProjectRecord.SUB_PROJECTS_FOLDER.equals(file2.getName())) {
									newProject.collectSubProjectFiles(file2, null, monitor);
									break;
								}
							}
						}						
					}
				}
				return true;
			}
		}
		// no project description found, so recurse into sub-directories
		for (int i = 0; i < contents.length; i++) {
			final File file = contents[i];
			if (file.isDirectory() && !METADATA_FOLDER.equals(file.getName())) {
				try {
					if (!directoriesVisited.add(file.getCanonicalPath())) {
						// already been here --> do not recurse
						continue;
					}
				} catch (IOException exception) {
					exception.printStackTrace();
				}
				collectProjectFilesFromDirectory(files, contents[i], directoriesVisited, monitor);
			}
		}
		return true;
	}

	/**
	 * Retrieve all the projects in the current workspace.
	 * 
	 * @return IProject[] array of IProject in the current workspace
	 */
	private static IProject[] getProjectsInWorkspace() {
		return ResourcesPlugin.getWorkspace().getRoot().getProjects();
	}

	/**
	 * Create the selected projects
	 * 
	 * @return boolean <code>true</code> if all project creations were
	 *         successful.
	 */
	public boolean createProjects() {
		// saveWidgetValues();
		final Object[] selected = projectsList.getCheckedElements();
		final WorkspaceModifyOperation op = new WorkspaceModifyOperation() {
			protected void execute(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
				try {
					monitor.beginTask("", selected.length); //$NON-NLS-1$
					if (monitor.isCanceled()) {
						throw new OperationCanceledException();
					}
					for (int i = 0; i < selected.length; i++) {
						final Object selectedObject = selected[i];
						if (selectedObject instanceof ProjectRecord) {
							ProjectRecord projectRecord = (ProjectRecord) selectedObject;
							if (projectRecord.hasSubProjects()) {
								Collection<ProjectRecord> subProj = projectRecord.getSubProjects();
								for (ProjectRecord subPprojectRecord : subProj) {
									if (!subPprojectRecord.hasWarnings())
										createExistingProject(subPprojectRecord, new SubProgressMonitor(monitor, 1));
								}
							}
							createExistingProject(projectRecord, new SubProgressMonitor(monitor, 1));

						} else if (selectedObject instanceof String) {
							// do nothing
						}
					}
				} finally {
					monitor.done();
				}
			}
		};
		// run the new project creation operation
		try {
			getContainer().run(true, true, op);
		} catch (InterruptedException e) {
			return false;
		} catch (InvocationTargetException e) {
			// one of the steps resulted in a core exception
			Throwable t = e.getTargetException();
			String message = "Creation Problems";
			IStatus status;
			if (t instanceof CoreException) {
				status = ((CoreException) t).getStatus();
			} else {
				status = new Status(IStatus.ERROR, "org.eclipse.ui.ide", 1, message, t);
			}
			ErrorDialog.openError(getShell(), message, null, status);
			ExamplePlugin.getDefault().logError(e);
			return false;
		}
		closeZipStructureProvider(structureProvider, getShell());
		return true;
	}

	/**
	 * Create the project described in record. If it is successful return true.
	 * 
	 * @param record
	 * @return boolean <code>true</code> if successful
	 * @throws InterruptedException
	 */
	private boolean createExistingProject(final ProjectRecord record, IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
		String projectName = record.getProjectName();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IProject project = workspace.getRoot().getProject(projectName);
		if (record.projectDescription == null) {
			// error case
			record.projectDescription = workspace.newProjectDescription(projectName);
			IPath locationPath = new Path(record.projectSystemFile.getAbsolutePath());

			// If it is under the root use the default location
			if (Platform.getLocation().isPrefixOf(locationPath)) {
				record.projectDescription.setLocation(null);
			} else {
				record.projectDescription.setLocation(locationPath);
			}
		} else {
			record.projectDescription.setName(projectName);
		}
		if (record.projectArchiveFile != null) {
			// import from archive
			List<ZipEntry> fileSystemObjects = structureProvider.getChildren(record.parent);
			structureProvider.setStrip(record.level);
			ImportOperation operation = new ImportOperation(project.getFullPath(), structureProvider.getRoot(), structureProvider, this, fileSystemObjects);
			operation.setContext(getShell());
			operation.run(monitor);
			return true;
		}

		// import from file system
		File importSource = null;
		// import project from location copying files - use default project
		// location for this workspace
		URI locationURI = record.projectDescription.getLocationURI();
		// if location is null, project already exists in this location or
		// some error condition occurred.
		if (locationURI != null) {
			importSource = new File(locationURI);
			IProjectDescription desc = workspace.newProjectDescription(projectName);
			desc.setBuildSpec(record.projectDescription.getBuildSpec());
			desc.setComment(record.projectDescription.getComment());
			desc.setDynamicReferences(record.projectDescription.getDynamicReferences());
			desc.setNatureIds(record.projectDescription.getNatureIds());
			desc.setReferencedProjects(record.projectDescription.getReferencedProjects());
			record.projectDescription = desc;
		}

		try {
			monitor.beginTask("Creating Projects", 100);
			project.create(record.projectDescription, new SubProgressMonitor(monitor, 30));
			project.open(IResource.BACKGROUND_REFRESH, new SubProgressMonitor(monitor, 70));
		} catch (CoreException e) {
			throw new InvocationTargetException(e);
		} finally {
			monitor.done();
		}

		// import operation to import project files if copy checkbox is selected
		if (importSource != null) {
			List<File> filesToImport = ExampleStructureProvider.INSTANCE.getChildren(importSource);

			if (record.hasSubProjects()) {
				for (Iterator<File> it = filesToImport.iterator(); it.hasNext();) {
					if (ProjectRecord.SUB_PROJECTS_FOLDER.equals(it.next().getName())) {
						it.remove();
						break;
					}
				}
			}

			ImportOperation operation = new ImportOperation(project.getFullPath(), importSource, ExampleStructureProvider.INSTANCE, this, filesToImport);
			operation.setContext(getShell());
			operation.setOverwriteResources(true); // need to overwrite
			// .project, .classpath
			// files
			operation.setCreateContainerStructure(false);
			operation.run(monitor);
		}
		return true;
	}

	/**
	 * The <code>WizardDataTransfer</code> implementation of this <code>IOverwriteQuery</code> method asks the user whether the existing
	 * resource at the given path should be overwritten.
	 * 
	 * @param pathString
	 * @return the user's reply: one of <code>"YES"</code>, <code>"NO"</code>, <code>"ALL"</code>, or <code>"CANCEL"</code>
	 */
	public String queryOverwrite(String pathString) {
		Path path = new Path(pathString);

		String messageString;
		// Break the message up if there is a file name and a directory
		// and there are at least 2 segments.
		if (path.getFileExtension() == null || path.segmentCount() < 2) {
			messageString = pathString + " already exists. Would you like to overwrite it?";
		} else {
			messageString = "Overwrite " + path.lastSegment() + " in folder " + path.removeLastSegments(1).toOSString() + " ?";
		}

		final MessageDialog dialog = new MessageDialog(getContainer().getShell(), "Question", null, messageString, MessageDialog.QUESTION, new String[] {
				IDialogConstants.YES_LABEL, IDialogConstants.YES_TO_ALL_LABEL, IDialogConstants.NO_LABEL, IDialogConstants.NO_TO_ALL_LABEL,
				IDialogConstants.CANCEL_LABEL }, 0);

		// run in syncExec because callback is from an operation,
		// which is probably not running in the UI thread.
		getControl().getDisplay().syncExec(new Runnable() {
			public void run() {
				dialog.open();
			}
		});
		return dialog.getReturnCode() < 0 ? CANCEL : response[dialog.getReturnCode()];
	}

	/**
	 * Performs clean-up if the user cancels the wizard without doing anything
	 */
	public void performCancel() {
		if (structureProvider != null)
			closeZipStructureProvider(structureProvider, getShell());
	}

	/* ****************************************************************
	 * HANDLE ZIP FILES
	 * ***************************************************************
	 */

	/**
	 * Determine whether the file with the given filename is in .zip or .jar
	 * format.
	 * 
	 * @param fileName
	 *            file to test
	 * @return true if the file is in tar format
	 */
	public static boolean isZipFile(String fileName) {
		if (fileName.length() == 0) {
			return false;
		}

		ZipFile zipFile = null;
		try {
			zipFile = new ZipFile(fileName);
		} catch (IOException ioException) {
			return false;
		} finally {
			if (zipFile != null) {
				try {
					zipFile.close();
				} catch (IOException e) {
					ExamplePlugin.getDefault().logError(e);
				}
			}
		}

		return true;
	}

	/**
	 * Closes the given structure provider. Attempts to close the passed zip
	 * file.
	 * 
	 * @param structureProvider
	 *            The structure provider to be closed, can be <code>null</code>
	 * @param shell
	 *            The shell to display any possible Dialogs in
	 */
	public static void closeZipStructureProvider(ZipStructureProvider structureProvider, Shell shell) {
		if (structureProvider == null)
			return;

		try {
			structureProvider.getZipFile().close();
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
		}
	}

	/* ****************************************************************
	 * PROJECT RECORD
	 * ***************************************************************
	 */

	/**
	 * Determine if the project with the given name is in the current workspace.
	 * 
	 * @param projectName
	 *            String the project name to check
	 * @return boolean true if the project with the given name is in this
	 *         workspace
	 */
	protected static boolean isProjectInWorkspace(String projectName) {
		if (projectName == null) {
			return false;
		}
		IProject[] workspaceProjects = getProjectsInWorkspace();
		for (int i = 0; i < workspaceProjects.length; i++) {
			if (projectName.equals(workspaceProjects[i].getName())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Class declared public only for test suite.
	 * 
	 */
	private class ProjectRecord {
		public static final String SUB_PROJECTS_FOLDER = "projects";
		
		private File projectSystemFile;

		private Collection<ProjectRecord> files;

		private Object projectArchiveFile;

		private String projectName;
		private CommentParser comment;
		private String warning = "";
		private String error = "";
		private boolean hasWarnings = false;
		private boolean hasErrors = false;

		private Object parent;

		private int level;

		private IProjectDescription projectDescription;

		/**
		 * Create a record for a project based on the info in the file.
		 * 
		 * @param file
		 */
		private ProjectRecord(File file) {
			projectSystemFile = file;
			setProjectName();
			performAlreadyExistsCheck();
			performRequirementCheck();
		}

		/**
		 * @param file
		 *            The Object representing the .project file
		 * @param parent
		 *            The parent folder of the .project file
		 * @param level
		 *            The number of levels deep in the provider the file is
		 */
		private ProjectRecord(Object file, Object parent, int level) {
			this.projectArchiveFile = file;
			this.parent = parent;
			this.level = level;
			setProjectName();
			performAlreadyExistsCheck();
			performRequirementCheck();
		}

		/**
		 * @param dir
		 * @param object
		 * @param monitor
		 */
		public void collectSubProjectFiles(File dir, Object object, IProgressMonitor monitor) {
			files = new LinkedList<ProjectRecord>();
			collectProjectFilesFromDirectory(files, dir, null, monitor);
		}

		public boolean hasSubProjects() {
			return !(files == null || files.isEmpty());
		}

		@SuppressWarnings("unchecked")
		public Collection<ProjectRecord> getSubProjects() {
			return (files != null) ? files : Collections.EMPTY_LIST;
		}

		/**
		 * Set the name of the project based on the projectFile.
		 */
		private void setProjectName() {
			try {
				if (projectArchiveFile != null) {
					InputStream stream = structureProvider.getContents(projectArchiveFile);

					// If we can get a description pull the name from there
					if (stream == null) {
						if (projectArchiveFile instanceof ZipEntry) {
							IPath path = new Path(((ZipEntry) projectArchiveFile).getName());
							projectName = path.segment(path.segmentCount() - 2);
						}
						comment = null;
					} else {
						projectDescription = ResourcesPlugin.getWorkspace().loadProjectDescription(stream);
						stream.close();
						projectName = projectDescription.getName();
						comment = new CommentParser(projectDescription.getComment());
					}

				}

				// If we don't have the project name try again
				if (projectName == null) {
					IPath path = new Path(projectSystemFile.getPath());
					// if the file is in the default location, use the directory
					// name as the project name
					if (isDefaultLocation(path)) {
						projectName = path.segment(path.segmentCount() - 2);
						projectDescription = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);
						comment = new CommentParser(projectDescription.getComment());
					} else {
						projectDescription = ResourcesPlugin.getWorkspace().loadProjectDescription(path);
						projectName = projectDescription.getName();
						comment = new CommentParser(projectDescription.getComment());
					}

				}
			} catch (CoreException e) {
				// no good couldn't get the name
				ExamplePlugin.getDefault().logError(e);
			} catch (IOException e) {
				// no good couldn't get the name
				ExamplePlugin.getDefault().logError(e);
			}
		}

		/**
		 * Returns whether the given project description file path is in the
		 * default location for a project
		 * 
		 * @param path
		 *            The path to examine
		 * @return Whether the given path is the default location for a project
		 */
		private boolean isDefaultLocation(IPath path) {
			// The project description file must at least be within the project,
			// which is within the workspace location
			if (path.segmentCount() < 2)
				return false;
			return path.removeLastSegments(2).toFile().equals(Platform.getLocation().toFile());
		}

		/**
		 * Get the name of the project
		 * 
		 * @return String
		 */
		public String getProjectName() {
			return projectName;
		}

		/**
		 * Get the description of the project
		 * 
		 * @return String
		 */
		public String getDescription() {
			return comment == null ? "" : comment.getDescription();
		}

		public boolean containsNatureID(String id) {
			for (String curID : projectDescription.getNatureIds()) {
				if (curID.equals(id)) {
					return true;
				}
			}
			return false;
		}

		public boolean hasWarnings() {
			return hasWarnings;
		}

		public String getWarningText() {
			return warning;
		}

		public boolean hasErrors() {
			return hasErrors;
		}

		public String getErrorText() {
			return error;
		}

		private void performAlreadyExistsCheck() {
			if (isProjectInWorkspace(getProjectName())) {
				error += "This example already exists in the workspace directory.";
				hasErrors = true;
			}
		}

		private void performRequirementCheck() {
			IStatus status = ResourcesPlugin.getWorkspace().validateNatureSet(projectDescription.getNatureIds());

			if (status.isOK()) {
				status = CorePlugin.getDefault().isComposable(projectDescription);
			}

			if (!status.isOK()) {
				warning = status.getMessage();
				if (status instanceof MultiStatus) {
					MultiStatus multi = (MultiStatus) status;
					if (multi.getChildren().length > 0) {
						warning += " (";
						for (int j = 0; j < multi.getChildren().length - 1; j++) {
							warning += multi.getChildren()[j].getMessage() + " ;";
						}
						warning += multi.getChildren()[multi.getChildren().length - 1].getMessage() + ")";
					}
				}
				hasWarnings = true;
			}
		}

		/**
		 * Gets the label to be used when rendering this project record in the
		 * UI.
		 * 
		 * @return String the label
		 * @since 3.4
		 */
		public String getProjectLabel() {
			return projectName;
		}
		
		@Override
		public int hashCode() {
			return projectName.hashCode();
		}

		@Override
		public boolean equals(Object arg) {
			return (arg instanceof ProjectRecord) && ((ProjectRecord) arg).projectName.equals(this.projectName);
		}
	}

}
