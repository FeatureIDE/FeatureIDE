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
package de.ovgu.featureide.fm.ui.views;

import static de.ovgu.featureide.fm.core.localization.StringTable.DISABLE_AUTOMATIC_CALCULATIONS;
import static de.ovgu.featureide.fm.core.localization.StringTable.START_CALCULATION;
import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATING_FEATURE_MODEL_EDITS;

import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.ViewContentProvider;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.ViewLabelProvider;

/**
 * A view to calculate the category an edit. Given an open feature model editor the current editing version is compared to the last saved model.
 *
 * @author Thomas Thuem
 * @author Marcus Pinnecke
 */
public class FeatureModelEditView extends ViewPart implements GUIDefaults {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.FeatureModelEditView";

	public static final Image REFESH_TAB_IMAGE = FMUIPlugin.getImage("refresh_tab.gif");

	private static final QualifiedName ACTIVATOR_KEY =
		new QualifiedName(FMUIPlugin.PLUGIN_ID + ".EditViewActivator", FMUIPlugin.PLUGIN_ID + ".EditViewActivator");

	private static final String ACTIVATOR_ACTION_TEXT = DISABLE_AUTOMATIC_CALCULATIONS;
	private static final String MANUAL_CALCULATION_TEXT = START_CALCULATION;

	private static final IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();

	private TreeViewer viewer;

	private FeatureModelEditor featureModelEditor;

	private Job job;

	/**
	 * Button to start manual calculations.
	 */
	private final Action manualAction = new Action() {

		@Override
		public void run() {
			final Job job = new Job(UPDATING_FEATURE_MODEL_EDITS) {

				@Override
				protected IStatus run(IProgressMonitor monitor) {
					if (featureModelEditor == null) {
						contentProvider.defaultContent();
					} else {
						contentProvider.calculateContent(featureModelEditor.getOriginalFeatureModel(), featureModelEditor.getFeatureModel(), monitor);
					}
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}
	};

	/**
	 * Button to enable/disable automatic calculations.
	 */
	private final Action activatorAction = new Action() {

		@Override
		public void run() {
			final Job job = new Job("") {

				@Override
				protected IStatus run(IProgressMonitor monitor) {
					activatorAction.setChecked(activatorAction.isChecked());
					manualAction.setEnabled(activatorAction.isChecked());
					setActivatorChecked(activatorAction.isChecked());
					return Status.OK_STATUS;
				}

			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}
	};

	private final IPartListener editorListener = new IPartListener() {

		@Override
		public void partOpened(IWorkbenchPart part) {}

		@Override
		public void partDeactivated(IWorkbenchPart part) {}

		@Override
		public void partClosed(IWorkbenchPart part) {
			if (part == featureModelEditor) {
				setFeatureModelEditor(null);
			}
		}

		@Override
		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart) {
				setFeatureModelEditor(part);
			}
		}

		@Override
		public void partActivated(IWorkbenchPart part) {
			if (part instanceof IEditorPart) {
				setFeatureModelEditor(part);
			}
		}

	};

	private final IEventListener modelListener = new IEventListener() {

		@Override
		public void propertyChange(FeatureIDEEvent evt) {
			switch (evt.getEventType()) {
			case CONSTRAINT_ADD:
			case CONSTRAINT_DELETE:
			case CONSTRAINT_MODIFY:
			case FEATURE_ADD:
			case FEATURE_ADD_ABOVE:
			case FEATURE_DELETE:
			case FEATURE_MODIFY:
			case GROUP_TYPE_CHANGED:
			case MANDATORY_CHANGED:
				refresh();
				break;
			default:
				break;
			}
		}
	};

	private final ViewContentProvider contentProvider = new ViewContentProvider(this);

	@Override
	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.setContentProvider(contentProvider);
		viewer.setLabelProvider(new ViewLabelProvider());
		viewer.setInput(getViewSite());

		getSite().getPage().addPartListener(editorListener);
		final IWorkbenchPage page = getSite().getPage();
		setFeatureModelEditor(page.getActiveEditor());

		fillLocalToolBar(getViewSite().getActionBars().getToolBarManager());
	}

	/**
	 * @param toolBarManager
	 */
	private void fillLocalToolBar(IToolBarManager manager) {
		manager.add(activatorAction);
		activatorAction.setChecked(isActivatorChecked());
		activatorAction.setToolTipText(ACTIVATOR_ACTION_TEXT);
		activatorAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));

		manager.add(manualAction);
		manualAction.setEnabled(activatorAction.isEnabled() && activatorAction.isChecked());
		manualAction.setToolTipText(MANUAL_CALCULATION_TEXT);
		manualAction.setImageDescriptor(ImageDescriptor.createFromImage(REFESH_TAB_IMAGE));
	}

	/**
	 * @return The persistent property status of the activator action
	 */
	private boolean isActivatorChecked() {
		try {
			return "true".equals(workspaceRoot.getPersistentProperty(ACTIVATOR_KEY));
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return true;
	}

	/**
	 * Sets the persistent property status of the activator action.
	 *
	 * @param checked The new status
	 */
	private void setActivatorChecked(boolean checked) {
		try {
			workspaceRoot.setPersistentProperty(ACTIVATOR_KEY, checked ? "true" : "false");
		} catch (final CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	public void dispose() {
		if (job != null) {
			if (job.getState() == Job.RUNNING) {
				job.cancel();
			}
			job = null;
		}
		getSite().getPage().removePartListener(editorListener);
		if (featureModelEditor != null) {
			featureModelEditor.removeEventListener(modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}
		super.dispose();
	}

	/**
	 * Passing the focus request to the viewer's control.
	 */
	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	private void setFeatureModelEditor(IWorkbenchPart activeEditor) {
		if ((featureModelEditor != null) && (featureModelEditor == activeEditor)) {
			return;
		}

		if (featureModelEditor != null) {
			featureModelEditor.removeEventListener(modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}

		if (activeEditor instanceof FeatureModelEditor) {
			featureModelEditor = (FeatureModelEditor) activeEditor;
			featureModelEditor.addEventListener(modelListener);
			featureModelEditor.getFeatureModel().addListener(modelListener);
		}
		refresh();
	}

	private void refresh() {
		if (contentProvider.isCanceled()) {
			return;
		}

		/*
		 * This job waits for the calculation job to finish and starts immediately a new one
		 */
		final Job waiter = new Job(UPDATING_FEATURE_MODEL_EDITS) {

			@Override
			protected IStatus run(IProgressMonitor monitor) {
				try {
					if (job != null) {
						if (contentProvider.isCanceled()) {
							return Status.OK_STATUS;
						}
						contentProvider.setCanceled(true);
						job.join();
						contentProvider.setCanceled(false);
					}
				} catch (final InterruptedException e) {
					FMUIPlugin.getDefault().logError(e);
				}

				job = new Job(UPDATING_FEATURE_MODEL_EDITS) {

					@Override
					protected IStatus run(IProgressMonitor monitor) {
						activatorAction.setEnabled(true);
						activatorAction.setChecked(isActivatorChecked());
						manualAction.setEnabled(isActivatorChecked());

						if (featureModelEditor == null) {
							contentProvider.defaultContent();
						} else if (isActivatorChecked()) {
							contentProvider.defaultManualContent();
						} else {
							contentProvider.calculateContent(featureModelEditor.getOriginalFeatureModel(), featureModelEditor.getFeatureModel(), monitor);
						}
						return Status.OK_STATUS;
					}
				};
				job.setPriority(Job.DECORATE);
				job.schedule();
				return Status.OK_STATUS;
			}
		};
		waiter.setPriority(Job.DECORATE);
		waiter.schedule();
	}

	public TreeViewer getViewer() {
		return viewer;
	}

}
