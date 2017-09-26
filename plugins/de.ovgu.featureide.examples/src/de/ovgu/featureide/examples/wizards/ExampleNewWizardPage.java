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
package de.ovgu.featureide.examples.wizards;

//import static de.ovgu.featureide.fm.core.localization.StringTable.NOT_ALL_PROJECT_SELECTED_;
import static de.ovgu.featureide.fm.core.localization.StringTable.PROJECTS_WITH_WARNINGS_ARE_SELECTED_;
//import static de.ovgu.featureide.fm.core.localization.StringTable.SELECTED_ONLY_FULLY_COMPATIBLE_PROJECTS_;
import static de.ovgu.featureide.fm.core.localization.StringTable.TYPE_FILTER_TEXT;

import java.text.CollationKey;
import java.text.Collator;
import java.util.Locale;
import java.util.Set;

import org.eclipse.core.runtime.IPath;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTreeViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.viewers.ViewerSorter;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Text;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.swt.widgets.ToolItem;
import org.eclipse.ui.dialogs.ContainerCheckedTreeViewer;

import de.ovgu.featureide.examples.utils.ProjectRecord;
import de.ovgu.featureide.fm.ui.FMUIPlugin;

/**
 * This class represents one page of the Example Wizard.
 *
 * @author Christian Becker
 * @author Reimar Schroeter
 */
public class ExampleNewWizardPage extends WizardPage {

	private static final Image IMAGE_EXPAND = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif").createImage();
	private static final Image IMAGE_COLLAPSE = FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif").createImage();
	private static final Image IMAGE_SELECT = FMUIPlugin.getDefault().getImageDescriptor("icons/select_all_icon.png").createImage();
	private static final Image IMAGE_DESELECT = FMUIPlugin.getDefault().getImageDescriptor("icons/deselect_all_icon.png").createImage();
	private static final Image IMAGE_HIDE_ERRORS = FMUIPlugin.getDefault().getImageDescriptor("icons/message_warning.gif").createImage();

	protected static final Color gray = new Color(null, 140, 140, 140);
	protected static final Color black = new Color(null, 0, 0, 0);

	private final SearchProjectFilter searchFilter = new SearchProjectFilter();
	private final ErrorProjectFilter errorFilter = new ErrorProjectFilter();

	private final ICheckStateListener checkStateList = new MyCheckStateListener();
	private final SelectionChangedListener selChangeList = new SelectionChangedListener();

	private ContainerTreeViewerWrapper wrapper;
	private Text descBox;
	private StyledText searchFeatureText;

	private abstract class ComposedViewerFilter extends ViewerFilter {

		public boolean selectComposer(Viewer viewer, Object parentElement, Object element) {
			final ViewerFilter[] filters = ((StructuredViewer) viewer).getFilters();
			Object[] filterRes = ((ITreeContentProvider) ((StructuredViewer) viewer).getContentProvider()).getChildren(element);
			for (final ViewerFilter viewerFilter : filters) {
				filterRes = viewerFilter.filter(viewer, element, filterRes);
			}
			return filterRes.length != 0;
		}
	}

	private class SearchProjectFilter extends ComposedViewerFilter {

		private String searchText = null;

		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			if (element instanceof ProjectRecord.TreeItem) {
				element = ((ProjectRecord.TreeItem) element).getRecord();
			}
			if ((searchText == null) || searchText.isEmpty() || TYPE_FILTER_TEXT.equals(searchFeatureText.getText())) {
				return true;
			} else if (element instanceof IPath) {
				return selectComposer(viewer, parentElement, element);
			} else if (element instanceof ProjectRecord) {
				return ((ProjectRecord) element).getProjectName().toLowerCase(Locale.ENGLISH).contains(searchText);
			} else {
				return false;
			}
		}
	}

	private class ErrorProjectFilter extends ComposedViewerFilter {

		private boolean isActive = false;

		@Override
		public boolean select(Viewer viewer, Object parentElement, Object element) {
			if (isActive) {
				if (element instanceof ProjectRecord.TreeItem) {
					final ProjectRecord projectRecord = ((ProjectRecord.TreeItem) element).getRecord();
					return !projectRecord.hasWarnings() && !projectRecord.hasErrors();
				}
				if (element instanceof IPath) {
					return selectComposer(viewer, parentElement, element);
				}
			}
			return true;
		}

		public void setActive(boolean isActive) {
			this.isActive = isActive;
		}
	};

	private class MyCheckStateListener implements ICheckStateListener {

		@Override
		public void checkStateChanged(CheckStateChangedEvent event) {
			if (event instanceof ContainerTreeViewerWrapper.ParentCheckStateChangedEvent) {
				CheckboxTreeViewer viewer = null;
				if (event.getSource() instanceof CheckboxTreeViewer) {
					viewer = (CheckboxTreeViewer) event.getSource();
				}

				if (event.getElement() instanceof ProjectRecord.TreeItem) {
					final ProjectRecord.TreeItem item = (ProjectRecord.TreeItem) event.getElement();
					if (viewer != null) {
						if (!viewer.getChecked(event.getElement()) || item.getRecord().hasWarnings()) {
							wrapper.setGrayed(item, true);
							wrapper.setChecked(item, false);
						}
					}
				}
			}
			if (event.getElement() instanceof ProjectRecord.TreeItem) {
				final ProjectRecord.TreeItem item = (ProjectRecord.TreeItem) event.getElement();
				if (item.getRecord().hasErrors()) {
					wrapper.setChecked(item, false);
				} else {
					if (event instanceof ContainerTreeViewerWrapper.ParentCheckStateChangedEvent) {
						final ContainerTreeViewerWrapper.ParentCheckStateChangedEvent newName = (ContainerTreeViewerWrapper.ParentCheckStateChangedEvent) event;
						if (newName.isOnlyRefresh()) {
							wrapper.setChecked(item, event.getChecked());
						}
					} else {
						wrapper.setChecked(item, event.getChecked());
					}
				}
			}
			determineAndSetPageComplete();
		}
	}

	private class SelectionChangedListener implements ISelectionChangedListener {

		@Override
		public void selectionChanged(SelectionChangedEvent event) {
			CheckboxTreeViewer viewer = null;
			ITreeContentProvider contProv = null;
			if (event.getSource() instanceof CheckboxTreeViewer) {
				viewer = (CheckboxTreeViewer) event.getSource();
			}
			if ((viewer != null) && (viewer.getContentProvider() instanceof ITreeContentProvider)) {
				contProv = (ITreeContentProvider) viewer.getContentProvider();
			}

			if (event.getSelection() instanceof IStructuredSelection) {
				final IStructuredSelection iss = (IStructuredSelection) event.getSelection();

				if (iss != null) {
					final Object selectedElement = iss.getFirstElement();
					if (selectedElement instanceof ProjectRecord.TreeItem) {
						final ProjectRecord.TreeItem treeItem = (ProjectRecord.TreeItem) selectedElement;
						final ProjectRecord tmpRecord = treeItem.getRecord();
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
					} else if (selectedElement instanceof IPath) {
						final Object[] checkedProjectItems = wrapper.getCheckedProjectItems(wrapper.getSelectedViewer());
						setMessage("");
						for (final Object object : checkedProjectItems) {
							final ProjectRecord.TreeItem item = (ProjectRecord.TreeItem) object;
							if (item.getRecord().hasWarnings()) {
								Object parent = contProv.getParent(item);
								while (parent != null) {
									if (parent.equals(selectedElement)) {
										setMessage(PROJECTS_WITH_WARNINGS_ARE_SELECTED_, WARNING);
										break;
									}
									parent = contProv.getParent(parent);
								}
							}
							if (!getMessage().isEmpty()) {
								break;
							}
						}
					}
				}
			}
		}
	}

	private class DynamicComposite extends Composite {

		public DynamicComposite(Composite parent, int style, String contentProviderName) {
			super(parent, style);
			final GridLayout layout = new GridLayout();
			setLayout(layout);
			setLayoutData(new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.FILL_BOTH));

			final ContainerCheckedTreeViewer contCheckTreeV = wrapper.getNewContainerViewer(this, SWT.BORDER);
			final GridData listData = new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.FILL_BOTH);
			contCheckTreeV.getControl().setLayoutData(listData);

			final IContentProvider contProv = new DynamicContentProvider(contentProviderName);
			contCheckTreeV.setContentProvider(contProv);
			contCheckTreeV.setLabelProvider(new ExampleLabelProvider());
			contCheckTreeV.addCheckStateListener(checkStateList);

			final ViewerSorter viewerSorter = new ViewerSorter(new Collator() {

				@Override
				public int hashCode() {
					return 0;
				}

				@Override
				public CollationKey getCollationKey(String arg0) {
					return null;
				}

				@Override
				public int compare(String arg0, String arg1) {
					return arg0.compareTo(arg1);
				}
			});

			contCheckTreeV.setSorter(viewerSorter);
			contCheckTreeV.addSelectionChangedListener(selChangeList);

			contCheckTreeV.setInput(ExampleNewWizardPage.this);
			setPageComplete(false);
		}
	}

	/**
	 * Constructor for SampleNewWizardPage.
	 *
	 * @param pageName
	 */
	public ExampleNewWizardPage() {
		super("");
		setTitle("Select FeatureIDE example(s) which you would like to explore");
	}

	@Override
	public void createControl(Composite parent) {
		ProjectProvider.resetProjectItems();
		initializeDialogUnits(parent);
		wrapper = new ContainerTreeViewerWrapper();

		final Composite workArea = new Composite(parent, SWT.NONE);
		setControl(workArea);

		GridLayout gridLayout = new GridLayout(1, false);
		gridLayout.verticalSpacing = 4;
		GridData gridData = new GridData();
		gridData.horizontalAlignment = SWT.FILL;
		gridData.grabExcessHorizontalSpace = true;
		gridData.grabExcessVerticalSpace = false;
		gridData.verticalAlignment = SWT.TOP;
		gridLayout = new GridLayout(3, false);
		gridLayout.marginHeight = 0;
		gridLayout.marginWidth = 0;
		gridLayout.marginLeft = 0;
		final Composite compositeTop = new Composite(workArea, SWT.NONE);
		compositeTop.setLayout(gridLayout);
		compositeTop.setLayoutData(gridData);

		searchFeatureText = new StyledText(compositeTop, SWT.SINGLE | SWT.LEFT | SWT.BORDER);
		searchFeatureText.setText(TYPE_FILTER_TEXT);

		gridData = new GridData();
		gridData.horizontalAlignment = SWT.RIGHT;
		gridData.verticalAlignment = SWT.CENTER;
		gridData.grabExcessHorizontalSpace = false;
		final ToolBar toolBar = new ToolBar(compositeTop, SWT.FLAT | SWT.WRAP | SWT.RIGHT);
		toolBar.setLayoutData(gridData);

		ToolItem item = new ToolItem(toolBar, SWT.CHECK);
		item.setImage(IMAGE_HIDE_ERRORS);
		item.setToolTipText("Hide all projects with errors and warnings");

		item.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (e.getSource() instanceof ToolItem) {
					final Object[] checkedProjects = wrapper.getCheckedProjectItems(wrapper.getSelectedViewer());
					errorFilter.setActive(((ToolItem) e.getSource()).getSelection());

					// Hack: Fix for gray state of parent
					wrapper.refreshAllViewers();
					wrapper.refreshCheckOfSelectedViewer(checkedProjects);

				}
			}
		});

		new ToolItem(toolBar, SWT.SEPARATOR);
		item = new ToolItem(toolBar, SWT.PUSH);
		item.setImage(IMAGE_COLLAPSE);
		item.setToolTipText("Collapse all projects");
		item.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				wrapper.getSelectedViewer().collapseAll();
			}
		});
		item = new ToolItem(toolBar, SWT.PUSH);
		item.setImage(IMAGE_EXPAND);
		item.setToolTipText("Expand all projects");
		item.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				wrapper.getSelectedViewer().expandAll();
			}
		});

		new ToolItem(toolBar, SWT.SEPARATOR);
		item = new ToolItem(toolBar, SWT.PUSH);
		item.setImage(IMAGE_SELECT);
		item.setToolTipText("Select All Projects");
		item.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				selectAllElementsWithoutWarningsAndErrors();
				determineAndSetPageComplete();
			}
		});
		item = new ToolItem(toolBar, SWT.PUSH);
		item.setImage(IMAGE_DESELECT);
		item.setToolTipText("Deselect All Projects");
		item.addSelectionListener(new SelectionAdapter() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				deselectAllProjects();
				setMessage("");
				determineAndSetPageComplete();
			}
		});

		createProjectSelectionArea(workArea);
		createDescriptionArea(workArea);

		searchFeatureText.setForeground(gray);
		searchFeatureText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
		searchFeatureText.addModifyListener(new ModifyListener() {

			@Override
			public void modifyText(ModifyEvent e) {
				final Object[] checkedProjects = wrapper.getCheckedProjectItems(wrapper.getSelectedViewer());
				searchFilter.searchText = searchFeatureText.getText().toLowerCase(Locale.ENGLISH);
				wrapper.refreshAllViewers();
				wrapper.refreshCheckOfSelectedViewer(checkedProjects);
			}
		});

		searchFeatureText.addListener(SWT.FocusOut, new Listener() {

			@Override
			public void handleEvent(Event event) {
				if (searchFeatureText.getText().isEmpty()) {
					searchFeatureText.setText(TYPE_FILTER_TEXT);
					searchFeatureText.setForeground(gray);
				}
			}
		});
		searchFeatureText.addListener(SWT.FocusIn, new Listener() {

			@Override
			public void handleEvent(Event event) {
				setMessage("");
				if (TYPE_FILTER_TEXT.equals(searchFeatureText.getText())) {
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
	private void createProjectSelectionArea(final Composite workArea) {
		final CTabFolder tabFolder = new CTabFolder(workArea, SWT.BORDER);
		tabFolder.addListener(SWT.MouseExit, new Listener() {

			@Override
			public void handleEvent(Event event) {
				final Object[] checkedProjects = wrapper.getCheckedProjects();
				boolean warningsExists = false;
				for (final Object object : checkedProjects) {
					final ProjectRecord rec = (ProjectRecord) object;
					if (rec.hasErrors() || rec.hasWarnings()) {
						setMessage(PROJECTS_WITH_WARNINGS_ARE_SELECTED_, IMessageProvider.WARNING);
						warningsExists = true;
						break;
					}
				}
				if (!warningsExists) {
					setMessage("");
				}
			}
		});
		tabFolder.setSimple(false);
		final GridLayout gridLayout = new GridLayout();

		tabFolder.setLayout(gridLayout);
		tabFolder.setLayoutData(new GridData(GridData.GRAB_HORIZONTAL | GridData.GRAB_VERTICAL | GridData.FILL_BOTH));

		tabFolder.addSelectionListener(new SelectionListener() {

			@Override
			public void widgetSelected(SelectionEvent e) {
				if (e.getSource() instanceof CTabFolder) {
					final CTabFolder tabFolder = (CTabFolder) e.getSource();
					final CTabItem selection = tabFolder.getSelection();
					final Control contr = selection.getControl();
					wrapper.setSelectedViewer(contr);
					final Object[] checkedProjects = wrapper.getCheckedProjectItems(wrapper.getSelectedViewer());
					wrapper.refreshCheckOfSelectedViewer(checkedProjects);
				}
			}

			@Override
			public void widgetDefaultSelected(SelectionEvent e) {}
		});

		final Set<String> tabItems = ProjectProvider.getViewersNamesForProjects();
		CTabItem item = null;
		for (final String name : tabItems) {
			item = new CTabItem(tabFolder, workArea.getStyle());
			item.setText(name);
			item.setControl(new DynamicComposite(tabFolder, SWT.MULTI, name));
			if (name.equals("Composer")) {
				tabFolder.setSelection(item);
				wrapper.setSelectedViewer(item.getControl());
			}
		}

		wrapper.addFilter(searchFilter);
		wrapper.addFilter(errorFilter);
	}

	private void createDescriptionArea(Composite workArea) {
		final Label title = new Label(workArea, SWT.NONE);
		title.setText("Description:");

		descBox = new Text(workArea, SWT.BORDER | SWT.MULTI | SWT.WRAP | SWT.READ_ONLY | SWT.V_SCROLL);
		descBox.setText("");

		final GridData dbDG = new GridData(GridData.FILL_BOTH);
		dbDG.minimumHeight = 75;
		descBox.setLayoutData(dbDG);
	}

	private void determineAndSetPageComplete() {
		setPageComplete(wrapper.isProjectSelected());
	}

	private void selectAllElementsWithoutWarningsAndErrors() {
		final Object[] allProjectItems = wrapper.getAllProjectItems(wrapper.getSelectedViewer());
		for (final Object object : allProjectItems) {
			if (object instanceof ProjectRecord.TreeItem) {
				final ProjectRecord.TreeItem treeItem = (ProjectRecord.TreeItem) object;
				if (!(treeItem.getRecord().hasErrors() || treeItem.getRecord().hasWarnings())) {
					wrapper.setChecked(treeItem, true);
				}
			}
		}
	}

	private void deselectAllProjects() {
		final Object[] checkedProjectItems = wrapper.getCheckedProjectItems(wrapper.getSelectedViewer());
		for (final Object object : checkedProjectItems) {
			wrapper.setChecked(object, false);
		}
	}

	public Object[] getCheckedProjects() {
		return wrapper.getCheckedProjects();
	}

}
