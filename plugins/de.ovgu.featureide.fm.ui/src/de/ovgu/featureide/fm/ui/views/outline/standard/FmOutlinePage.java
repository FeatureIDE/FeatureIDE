/* FeatureIDE - A Framework for Feature-Oriented Software Development
 * Copyright (C) 2005-2019  FeatureIDE team, University of Magdeburg, Germany
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
package de.ovgu.featureide.fm.ui.views.outline.standard;

import static de.ovgu.featureide.fm.core.localization.StringTable.UPDATE_OUTLINE_VIEW;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.ovgu.featureide.fm.core.base.event.FeatureIDEEvent;
import de.ovgu.featureide.fm.core.base.event.IEventListener;
import de.ovgu.featureide.fm.core.io.manager.FeatureModelManager;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.views.outline.FmOutlinePageContextMenu;
import de.ovgu.featureide.fm.ui.views.outline.custom.providers.FMLabelProvider;
import de.ovgu.featureide.fm.ui.views.outline.custom.providers.FMTreeContentProvider;

/**
 * This class is part of the outline. It sets up an new outline page that uses a TreeView to show the FeatureModel currently being worked on.
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke
 */
public class FmOutlinePage extends ContentOutlinePage implements IEventListener {

	protected FeatureModelManager fmManager;

	protected FeatureModelEditor fTextEditor;

	private TreeViewer viewer;

	private FmOutlinePageContextMenu contextMenu;

	private UIJob updateOutlineJob;

	private FMTreeContentProvider contentProvider;

	private FMLabelProvider labelProvider;

	public FmOutlinePage(IDocumentProvider documentProvider, FeatureModelEditor editor) {
		super();
		fTextEditor = editor;
	}

	/**
	 * Sets the input of the outline page
	 *
	 * @param input the input of this outline page
	 */
	public void setInput(FeatureModelManager fmManager) {
		this.fmManager = fmManager;
		fmManager.addListener(this);
		update(((FileEditorInput) fTextEditor.getEditorInput()).getFile());
	}

	/**
	 * Sets the new input or disables the viewer in case no editor is open
	 *
	 */
	private void update(final IFile iFile) {
		if (viewer != null) {
			final Control control = viewer.getControl();
			if ((control != null) && !control.isDisposed()) {

				if ((updateOutlineJob == null) || (updateOutlineJob.getState() == Job.NONE)) {
					updateOutlineJob = new UIJob(UPDATE_OUTLINE_VIEW) {

						@Override
						public IStatus runInUIThread(IProgressMonitor monitor) {

							if (viewer != null) {
								if ((viewer.getControl() != null) && !viewer.getControl().isDisposed()) {
									viewer.getControl().setRedraw(false);

									viewer.setContentProvider(contentProvider);
									viewer.setLabelProvider(labelProvider);
									if (iFile != null) {
										viewer.setInput(iFile);
										viewer.getContentProvider().inputChanged(viewer, null, fmManager);
										if (fTextEditor.getEditorInput() instanceof FeatureModelEditor) {
											if ((contextMenu == null)
												|| (contextMenu.getFeatureModelManager() != ((FeatureModelEditor) fTextEditor.getEditorInput())
														.getFeatureModelManager())) {
												contextMenu = new FmOutlinePageContextMenu(getSite(), (FeatureModelEditor) fTextEditor.getEditorInput(), viewer,
														((FeatureModelEditor) fTextEditor.getEditorInput()).getFeatureModelManager(), false);
											}
										}
									}

									viewer.getControl().setRedraw(true);
									viewer.getControl().setEnabled(true);
									viewer.refresh();
								}
							}
							return Status.OK_STATUS;
						}
					};
					updateOutlineJob.setPriority(Job.SHORT);
					updateOutlineJob.schedule();
				}
			}
		}
	}

	@Override
	public void createControl(Composite parent) {
		super.createControl(parent);
		if (viewer == null) {
			viewer = getTreeViewer();
			contentProvider = new FMTreeContentProvider();
			viewer.setContentProvider(contentProvider);
			labelProvider = new FMLabelProvider();
			viewer.setLabelProvider(labelProvider);
		}

		if (fmManager != null) {
			update(((FileEditorInput) fTextEditor.getEditorInput()).getFile());
		}

		viewer.expandToLevel(2);
		final FmOutlinePageContextMenu cm = new FmOutlinePageContextMenu(getSite(), fTextEditor, viewer, fmManager);
		cm.addToolbar(getSite().getActionBars().getToolBarManager());
	}

	@Override
	public void propertyChange(FeatureIDEEvent event) {
		switch (event.getEventType()) {
		case MODEL_DATA_OVERWRITTEN:
		case MODEL_DATA_CHANGED:
		case MODEL_DATA_SAVED:
		case MANDATORY_CHANGED:
		case GROUP_TYPE_CHANGED:
		case FEATURE_NAME_CHANGED:
		case FEATURE_ADD_SIBLING:
		case FEATURE_ADD:
		case FEATURE_ADD_ABOVE:
		case FEATURE_DELETE:
		case CONSTRAINT_MODIFY:
		case CONSTRAINT_DELETE:
		case CONSTRAINT_ADD:
		case FEATURE_COLLAPSED_CHANGED:
		case FEATURE_COLLAPSED_ALL_CHANGED:
			update(((FileEditorInput) fTextEditor.getEditorInput()).getFile());
			break;
		default:
			break;
		}
	}

}
