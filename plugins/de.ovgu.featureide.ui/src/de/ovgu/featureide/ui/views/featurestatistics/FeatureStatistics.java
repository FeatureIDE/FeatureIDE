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
package de.ovgu.featureide.ui.views.featurestatistics;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import de.ovgu.featureide.ui.UIPlugin;
import de.ovgu.featureide.ui.views.collaboration.model.Collaboration;
import de.ovgu.featureide.ui.views.collaboration.model.CollaborationModel;
import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.FeatureModel;
import de.ovgu.featureide.fm.core.PropertyConstants;
import de.ovgu.featureide.fm.core.editing.evaluation.Evaluation;
import de.ovgu.featureide.fm.core.io.FeatureModelReaderIFileWrapper;
import de.ovgu.featureide.fm.core.io.UnsupportedModelException;
import de.ovgu.featureide.fm.core.io.xml.XmlFeatureModelReader;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GEFImageWriter;
import de.ovgu.featureide.fm.ui.editors.featuremodel.GUIDefaults;
import de.ovgu.featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import de.ovgu.featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;
import de.ovgu.featureide.fm.ui.views.featuremodeleditview.ViewLabelProvider;

public class FeatureStatistics extends ViewPart implements GUIDefaults {

	public static final String ID = UIPlugin.PLUGIN_ID
			+ ".views.FeatureStatistics";
	public static final Image REFESH_TAB_IMAGE = FMUIPlugin
			.getImage("refresh_tab.gif");
	private static final QualifiedName ACTIVATOR_KEY = new QualifiedName(
			FMUIPlugin.PLUGIN_ID + ".EditViewActivator", FMUIPlugin.PLUGIN_ID
					+ ".EditViewActivator");
	private FeatureModelEditor featureModelEditor;
	private static final IWorkspaceRoot workspaceRoot = ResourcesPlugin
			.getWorkspace().getRoot();
	private TreeViewer viewer;
	private StatisticsContentProvider contentProvider = new StatisticsContentProvider(
			this);
	private Job job;
	public static IFile inputFile;
	public static IFeatureProject featureProject;
	public void dispose() {
		if (job != null) {
			if (job.getState() == Job.RUNNING)
				job.cancel();
			job = null;
		}
		getSite().getPage().removePartListener(editorListener);
		if (featureModelEditor != null) {
			featureModelEditor.getOriginalFeatureModel().removeListener(
					modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}
		super.dispose();
	}

	private Action manualAction = new Action() {
		public void run() {
			Job job = new Job("Updating Feature Model Edits") {
				protected IStatus run(IProgressMonitor monitor) {
					if (featureModelEditor == null)
						contentProvider.defaultContent();
					else {

					}
					return Status.OK_STATUS;
				}
			};
			job.setPriority(Job.SHORT);
			job.schedule();
		}
	};

	private void refresh() {
		if (contentProvider.isCanceled()) {
			return;
		}

		/*
		 * This job waits for the calculation job to finish and starts
		 * immediately a new one
		 */
		Job waiter = new Job("Updating Feature Model Edits") {
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
				} catch (InterruptedException e) {
					FMUIPlugin.getDefault().logError(e);
				}

				job = new Job("Updating Feature Model Edits") {
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
							featureProject = CorePlugin.getFeatureProject(featureModelEditor.getGrammarFile().getResource().getProject());
							
							contentProvider.getFeatureModelSpecification(featureModelEditor.getFeatureModel());
							contentProvider.print();

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

	private Action activatorAction = new Action() {
		public void run() {
			Job job = new Job("") {
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

	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
			if (part == featureModelEditor)
				setFeatureModelEditor(null);
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setFeatureModelEditor(part);
		}

		public void partActivated(IWorkbenchPart part) {
		}

	};

	private PropertyChangeListener modelListener = new PropertyChangeListener() {
		public void propertyChange(PropertyChangeEvent evt) {
			if (!evt.getPropertyName().equals(
					PropertyConstants.MODEL_LAYOUT_CHANGED))
				refresh();
		}
	};

	private void setFeatureModelEditor(IWorkbenchPart activeEditor) {
		featureProject = CorePlugin.getFeatureProject(((FileEditorInput)((IEditorPart) activeEditor).getEditorInput()).getFile());
		if (featureModelEditor != null && featureModelEditor == activeEditor)
			return;

		if (featureModelEditor != null) {
			featureModelEditor.getOriginalFeatureModel().removeListener(
					modelListener);
			
			
			featureModelEditor = null;
		}

		if (activeEditor instanceof FeatureModelEditor) {
			featureModelEditor = (FeatureModelEditor) activeEditor;
			
			featureModelEditor.getFeatureModel().addListener(modelListener);

			if (evaluation == null
					&& featureModelEditor.getGrammarFile().getResource()
							.getProject().getName()
							.startsWith("EvaluationTest")) {
				evaluation = new Job("Evaluation Test") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						Evaluation.evaluate(featureModelEditor.getGrammarFile()
								.getResource().getProject());
						return Status.OK_STATUS;
					}
				};
				evaluation.setPriority(Job.LONG);
				evaluation.schedule();
				UIJob conversion = new UIJob("Converting Feature Models") {
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						try {
							convertModelToBitmapTest(featureModelEditor
									.getGrammarFile().getResource()
									.getProject().getFolder("models"));
						} catch (Exception e) {
							FMUIPlugin.getDefault().logError(e);
						}
						return Status.OK_STATUS;
					}

					public void convertModelToBitmapTest(IFolder folder)
							throws CoreException {
						for (IResource res : folder.members())
							if (res instanceof IFile
									&& res.getName().endsWith(".m")) {
								IFile fmFile = (IFile) res;
								try {
									FeatureModel fm = new FeatureModel();

									FeatureModelReaderIFileWrapper reader = new FeatureModelReaderIFileWrapper(
											new XmlFeatureModelReader(fm));
									reader.readFromFile(fmFile);

									String imageName = fmFile.getRawLocation()
											.toOSString();
									imageName = imageName.substring(0,
											imageName.length() - ".m".length())
											+ ".png";
									createBitmap(fm, new File(imageName));
								} catch (FileNotFoundException e) {
									FMUIPlugin.getDefault().logError(e);
								} catch (UnsupportedModelException e) {
									FMUIPlugin.getDefault().logError(e);
								}
							}
						folder.refreshLocal(IResource.DEPTH_ONE, null);
					}

					private void createBitmap(FeatureModel featureModel,
							File file) {
						GraphicalViewerImpl graphicalViewer = new ScrollingGraphicalViewer();
						graphicalViewer.createControl(viewer.getControl()
								.getParent());
						graphicalViewer.getControl().setBackground(
								DIAGRAM_BACKGROUND);
						graphicalViewer
								.setEditPartFactory(new GraphicalEditPartFactory());
						ScalableFreeformRootEditPart rootEditPart = new ScalableFreeformRootEditPart();
						((ConnectionLayer) rootEditPart
								.getLayer(LayerConstants.CONNECTION_LAYER))
								.setAntialias(SWT.ON);
						graphicalViewer.setRootEditPart(rootEditPart);
						graphicalViewer.setContents(featureModel);
						FeatureDiagramLayoutManager layoutManager = new LevelOrderLayout();
						layoutManager.layout(featureModel);
						GEFImageWriter.writeToFile(graphicalViewer, file);
					}
				};
				conversion.setPriority(Job.LONG);
				conversion.schedule();
			}
		}else{
			IEditorPart part = (IEditorPart) activeEditor;
			inputFile = ((FileEditorInput)part.getEditorInput()).getFile();
			featureProject = CorePlugin.getFeatureProject(inputFile);
			
			
			contentProvider.getFeatureModelSpecification(featureProject.getFeatureModel());
					contentProvider.print();
			
		
		}			
		refresh();
	}

	private boolean isActivatorChecked() {
		try {
			return "true".equals(workspaceRoot
					.getPersistentProperty(ACTIVATOR_KEY));
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
		return true;
	}

	private void setActivatorChecked(boolean checked) {
		try {
			workspaceRoot.setPersistentProperty(ACTIVATOR_KEY, checked ? "true"
					: "false");
		} catch (CoreException e) {
			FMUIPlugin.getDefault().logError(e);
		}
	}

	@Override
	/**
	 * Passing the focus request to the viewer's control.
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	private Job evaluation;

	public TreeViewer getViewer() {
		return viewer;
	}

	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.setContentProvider(contentProvider);
		viewer.setLabelProvider(new ViewLabelProvider());
		viewer.setInput(getViewSite());

		getSite().getPage().addPartListener(editorListener);
		IWorkbenchPage page = getSite().getPage();
		setFeatureModelEditor(page.getActiveEditor());
	}

}
