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
package de.ovgu.featureide.examples.wizards;

import static de.ovgu.featureide.fm.core.localization.StringTable.CHILDREN_COULD_NOT_BE_LOADED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATING_PROJECTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATION_PROBLEMS;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXAMPLES_COULD_NOT_BE_LOADED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.IN_FOLDER;
import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_ALL_PROJECT_SELECTED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.OVERWRITE;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROCESSING_RESULTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECTS_WITH_WARNINGS_ARE_SELECTED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.QUESTION;
import static de.ovgu.featureide.fm.core.localization.StringTable.SEARCHING_FOR_PROJECTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_ONLY_FULLY_COMPATIBLE_PROJECTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE_FILTER_TEXT;

import java.io.IOException;
import java.io.InputStream;
import java.io.ObjectInputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Set;

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
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Path;
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
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.TreeItem;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.eclipse.ui.wizards.datatransfer.ImportOperation;

import de.ovgu.featureide.core.builder.ComposerExtensionManager;
import de.ovgu.featureide.core.builder.IComposerExtensionBase;
import de.ovgu.featureide.examples.ExamplePlugin;
import de.ovgu.featureide.examples.utils.ProjectRecord;
import de.ovgu.featureide.examples.utils.SimpleStructureProvider;

/**
 * This class represents one page of the Example Wizard.
 * 
 * @author Christian Becker
 * @author Reimar Schroeter
 */
public class ExampleNewWizardPage extends WizardPage implements IOverwriteQuery {
	Collection<ProjectRecord> projects = null;

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

	private ItemAccessCheckboxTreeViewer projectsList;
	private Text descBox;

	private Hashtable<String, List<ProjectRecord>> compTable;
	//	private String samplePath;

	private static final String[] response = new String[] { YES, ALL, NO, NO_ALL, CANCEL };
	private static final String FILTERTEXT = TYPE_FILTER_TEXT;

	private StyledText searchFeatureText;
	private final ExampleProjectFilter searchFilter = new ExampleProjectFilter();

	private static final String CHILD_WARNING = SELECTED_ONLY_FULLY_COMPATIBLE_PROJECTS_ + "(Manual selection for projects with warnings is still possible).";

	private Thread updateProjects;

	/**
	 * Constructor for SampleNewWizardPage.
	 * 
	 * @param pageName
	 */
	public ExampleNewWizardPage() {
		super("Select FeatureIDE Example(s)");
		setTitle("Select FeatureIDE example(s) which you would like to explore");
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
					return new Object[] { CHILDREN_COULD_NOT_BE_LOADED_ };
				}
			}

			public Object[] getElements(Object inputElement) {
				if (inputElement == null) {
					return new String[] { "Loading..." };
				} else if (inputElement == exampleNewWizardPage) {
					updateProjectsList();
					if (updateProjects != null) {
						try {
							updateProjects.join();
						} catch (InterruptedException e) {
							ExamplePlugin.getDefault().logError(e);
						}
						return compTable.keySet().toArray();
					} else {
						return new Object[] { EXAMPLES_COULD_NOT_BE_LOADED_ };
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
										setMessage(PROJECTS_WITH_WARNINGS_ARE_SELECTED_, WARNING);
										allProjectsSelected = true;
										break;
									}
									if (!currItem.getChecked() && !project.hasErrors()) {
										allProjectsSelected = false;
									}
								}
							}
							if (!allProjectsSelected && treeItem.getChecked()) {
								setMessage(NOT_ALL_PROJECT_SELECTED_, INFORMATION);
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
	public void updateProjectsList() {
		updateProjects = new Thread(new Runnable() {
			public void run() {
				NullProgressMonitor monitor = new NullProgressMonitor();
				monitor.beginTask(SEARCHING_FOR_PROJECTS, 100);
				Iterator<ProjectRecord> filesIterator = null;

				monitor.worked(10);

				URL url = null;
				InputStream inputStream = null;
				try {
					url = new URL("platform:/plugin/de.ovgu.featureide.examples/projects.s");
					inputStream = url.openConnection().getInputStream();
				} catch (IOException e) {
					e.printStackTrace();
				}

				if (!getProjects(inputStream)) {
					return;
				}
				filesIterator = projects.iterator();

				monitor.worked(50);
				if (filesIterator != null) {
					monitor.subTask(PROCESSING_RESULTS);
					compTable = new Hashtable<String, List<ProjectRecord>>();
					while (filesIterator.hasNext()) {
						ProjectRecord pr = filesIterator.next();
						String compID = "", composer = "";

						for (ICommand command : pr.getProjectDescription().getBuildSpec()) {
							if (command.getArguments().containsKey("composer")) {
								compID = command.getArguments().get("composer");
								composer = compID.substring(compID.lastIndexOf(".") + 1);
								if (!compTable.containsKey(composer)) {
									compTable.put(composer, new LinkedList<ProjectRecord>());
								}
								compTable.get(composer).add(pr);
								break;
							}
						}
					}
				}
				monitor.done();
			}

			@SuppressWarnings("unchecked")
			private boolean getProjects(InputStream inputStream) {
				if (projects == null) {
					try (ObjectInputStream stream = new ObjectInputStream(inputStream)) {
						Object res = stream.readObject();
						projects = ((Collection<ProjectRecord>) res);
					} catch (IOException | ClassNotFoundException | ClassCastException e) {
						ExamplePlugin.getDefault().logError(e);
						return false;
					}

					for (ProjectRecord projectRecord : projects) {
						projectRecord.init();
					}
				}
				return true;
			}
		});
		updateProjects.start();
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
			String message = CREATION_PROBLEMS;
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
		return true;
	}

	/**
	 *
	 * Create the project described in record. If it is successful return true.
	 * 
	 * @param record
	 * @return boolean <code>true</code> if successful
	 * @throws InvocationTargetException
	 * @throws InterruptedException
	 * @throws IOException
	 */
	@SuppressWarnings("unchecked")
	private boolean createExistingProject(final ProjectRecord record, IProgressMonitor monitor) throws InvocationTargetException, InterruptedException {
		String projectName = record.getProjectName();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IProject project = workspace.getRoot().getProject(projectName);

		URL url = null;
		InputStream inputStream = null;
		try {
			url = new URL("platform:/plugin/de.ovgu.featureide.examples/" + record.getIndexPath());
			inputStream = url.openConnection().getInputStream();
		} catch (IOException e) {
			ExamplePlugin.getDefault().logError(e);
			return false;
		}

		try (ObjectInputStream instr = new ObjectInputStream(inputStream);) {
			Object in = instr.readObject();
			List<String> res = (List<String>) in;

			ImportOperation operation = new ImportOperation(project.getFullPath(), res.get(0), new SimpleStructureProvider(record.getProjectName()), this, res);
			operation.run(monitor);
			if (record.hasSubProjects()) {
				for (ProjectRecord sub : record.getSubProjects()) {
					importSubProjects(sub, monitor);
				}
			}
		} catch (IOException | ClassNotFoundException | ClassCastException e) {
			ExamplePlugin.getDefault().logError(e);
			return false;
		}
		return true;
	}

	/**
	 * @param record
	 * @param monitor
	 * @param projectName
	 * @param workspace
	 * @param project
	 * @throws InvocationTargetException
	 */
	private void importSubProjects(final ProjectRecord record, IProgressMonitor monitor) throws InvocationTargetException {
		String projectName = record.getProjectName();
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		final IProject project = workspace.getRoot().getProject(projectName);

		IProjectDescription desc = workspace.newProjectDescription(projectName);
		desc.setBuildSpec(record.getProjectDescription().getBuildSpec());
		desc.setComment(record.getProjectDescription().getComment());
		desc.setDynamicReferences(record.getProjectDescription().getDynamicReferences());
		desc.setNatureIds(record.getProjectDescription().getNatureIds());
		desc.setReferencedProjects(record.getProjectDescription().getReferencedProjects());

		final String projectPath = record.getRelativeLocation();
		IPath location = workspace.getRoot().getLocation();
		location = location.append(projectPath);
		desc.setLocation(location);

		try {
			monitor.beginTask(CREATING_PROJECTS, 100);
			project.create(desc, new SubProgressMonitor(monitor, 30));
			project.open(IResource.BACKGROUND_REFRESH, new SubProgressMonitor(monitor, 70));
		} catch (CoreException e) {
			throw new InvocationTargetException(e);
		} finally {
			monitor.done();
		}
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
			messageString = OVERWRITE + path.lastSegment() + IN_FOLDER + path.removeLastSegments(1).toOSString() + " ?";
		}

		final MessageDialog dialog = new MessageDialog(getContainer().getShell(), QUESTION, null, messageString, MessageDialog.QUESTION,
				new String[] { IDialogConstants.YES_LABEL, IDialogConstants.YES_TO_ALL_LABEL, IDialogConstants.NO_LABEL, IDialogConstants.NO_TO_ALL_LABEL,
						IDialogConstants.CANCEL_LABEL },
				0);

		// run in syncExec because callback is from an operation,
		// which is probably not running in the UI thread.
		getControl().getDisplay().syncExec(new Runnable() {
			public void run() {
				dialog.open();
			}
		});
		return dialog.getReturnCode() < 0 ? CANCEL : response[dialog.getReturnCode()];
	}
}
