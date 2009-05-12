/* FeatureIDE - An IDE to support feature-oriented software development
 * Copyright (C) 2005-2009  FeatureIDE Team, University of Magdeburg
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
package featureide.fm.ui.views;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileNotFoundException;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.draw2d.ConnectionLayer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.ScalableFreeformRootEditPart;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.gef.ui.parts.ScrollingGraphicalViewer;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;
import org.eclipse.ui.progress.UIJob;

import featureide.fm.core.FeatureModel;
import featureide.fm.core.editing.evaluation.Evaluation;
import featureide.fm.core.io.UnsupportedModelException;
import featureide.fm.core.io.guidsl.FeatureModelReader;
import featureide.fm.ui.FMUIPlugin;
import featureide.fm.ui.editors.FeatureModelEditor;
import featureide.fm.ui.editors.featuremodel.GEFImageWriter;
import featureide.fm.ui.editors.featuremodel.GUIDefaults;
import featureide.fm.ui.editors.featuremodel.editparts.GraphicalEditPartFactory;
import featureide.fm.ui.editors.featuremodel.layouts.FeatureDiagramLayoutManager;
import featureide.fm.ui.editors.featuremodel.layouts.LevelOrderLayout;
import featureide.fm.ui.views.featuremodeleditview.ViewContentProvider;
import featureide.fm.ui.views.featuremodeleditview.ViewLabelProvider;

/**
 * A view to calculate the category an edit. Given an open feature model editor
 * the current editing version is compared to the last saved model.
 * 
 * @author Thomas Thuem
 */
public class FeatureModelEditView extends ViewPart {

	public static final String ID = FMUIPlugin.PLUGIN_ID + ".views.FeatureModelEditView";

	private TreeViewer viewer;

	private FeatureModelEditor featureModelEditor;

	private Job job;

	private IPartListener editorListener = new IPartListener() {

		public void partOpened(IWorkbenchPart part) {
		}

		public void partDeactivated(IWorkbenchPart part) {
		}

		public void partClosed(IWorkbenchPart part) {
			if (part == featureModelEditor)
				setGrammarEditor(null);
		}

		public void partBroughtToTop(IWorkbenchPart part) {
			if (part instanceof IEditorPart)
				setGrammarEditor(part);
		}

		public void partActivated(IWorkbenchPart part) {
		}

	};

	private PropertyChangeListener modelListener = new PropertyChangeListener() {
		public void propertyChange(PropertyChangeEvent evt) {
			refresh();
		}
	};

	private ViewContentProvider contentProvider = new ViewContentProvider(this);

	public void createPartControl(Composite parent) {
		viewer = new TreeViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
		viewer.setContentProvider(contentProvider);
		viewer.setLabelProvider(new ViewLabelProvider());
		viewer.setInput(getViewSite());

		getSite().getPage().addPartListener(editorListener);
		IWorkbenchPage page = getSite().getPage();
		setGrammarEditor(page.getActiveEditor());
	}

	@Override
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

	/**
	 * Passing the focus request to the viewer's control.
	 */
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	private Job evaluation;

	private void setGrammarEditor(IWorkbenchPart activeEditor) {
		if (featureModelEditor == activeEditor)
			return;

		if (featureModelEditor != null) {
			featureModelEditor.getOriginalFeatureModel().removeListener(
					modelListener);
			featureModelEditor.getFeatureModel().removeListener(modelListener);
			featureModelEditor = null;
		}

		if (activeEditor instanceof FeatureModelEditor) {
			featureModelEditor = (FeatureModelEditor) activeEditor;
			featureModelEditor.getOriginalFeatureModel().addListener(modelListener);
			featureModelEditor.getFeatureModel().addListener(modelListener);

			if (evaluation == null && featureModelEditor != null && featureModelEditor.getGrammarFile().getResource().getProject().getName().startsWith("EvaluationTest")) {
				evaluation = new Job("Evaluation Test") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
						Evaluation.evaluate(featureModelEditor.getGrammarFile().getResource().getProject());
						return Status.OK_STATUS;
					}
				};
				evaluation.setPriority(Job.LONG);
				evaluation.schedule();
				UIJob conversion = new UIJob("Converting Feature Models") {
					@Override
					public IStatus runInUIThread(IProgressMonitor monitor) {
						try {
							convertModelToBitmapTest(featureModelEditor.getGrammarFile().getResource().getProject().getFolder("models"));
						} catch (Exception e) {
							e.printStackTrace();
						}
						return Status.OK_STATUS;
					}

					public void convertModelToBitmapTest(IFolder folder) throws CoreException {
						for (IResource res : folder.members())
							if (res instanceof IFile && res.getName().endsWith(".m")) {
								IFile fmFile = (IFile) res;
								try {
									FeatureModel fm = new FeatureModel();
									FeatureModelReader reader = new FeatureModelReader(fm);
									reader.readFromFile(fmFile);

									String imageName = fmFile.getRawLocation().toOSString();
									imageName = imageName.substring(0, imageName.length()-".m".length()) + ".png";
									createBitmap(fm, new File(imageName));
								} catch (FileNotFoundException e) {
									e.printStackTrace();
								} catch (UnsupportedModelException e) {
									e.printStackTrace();
								}
							}
						folder.refreshLocal(IResource.DEPTH_ONE, null);
					}

					private void createBitmap(FeatureModel featureModel, File file) {
						GraphicalViewerImpl graphicalViewer = new ScrollingGraphicalViewer();
						graphicalViewer.createControl(viewer.getControl().getParent());
						graphicalViewer.getControl().setBackground(GUIDefaults.DIAGRAM_BACKGROUND);
						graphicalViewer.setEditPartFactory(new GraphicalEditPartFactory());
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
		}

		refresh();
	}

	private void refresh() {
		if (job != null && job.getState() == Job.RUNNING)
			job.cancel();

		job = new Job("Updating Feature Model Edits") {
			@Override
			protected IStatus run(IProgressMonitor monitor) {
				if (featureModelEditor == null)
					contentProvider.defaultContent();
				else
					contentProvider.calculateContent(featureModelEditor.getOriginalFeatureModel(), featureModelEditor.getFeatureModel());
				return Status.OK_STATUS;
			}
		};
		job.setPriority(Job.LONG);
		job.schedule();
	}

	public TreeViewer getViewer() {
		return viewer;
	}

}
