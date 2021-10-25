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
package de.ovgu.featureide.fm.ui.views.outline;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPAND_ALL;

import java.util.Spliterator;
import java.util.stream.StreamSupport;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.part.IPageSite;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.MultiFeatureModel;
import de.ovgu.featureide.fm.core.io.manager.IFeatureModelManager;
import de.ovgu.featureide.fm.core.io.manager.IManager;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.fm.ui.views.outline.custom.action.RemoveImportedFeatureModelsAction;

/**
 * Context Menu for Outline view of FeatureModels
 *
 * @author Jan Wedding
 * @author Melanie Pflaume
 * @author Marcus Pinnecke
 * @author Paul Maximilian Bittner
 * @author Niklas Lehnfeld
 * @author Mohammed Mahhouk
 */
public class FmOutlinePageContextMenu {

	private final Object site;
	private FeatureModelEditor fTextEditor;
	private final TreeViewer viewer;
	private final IFeatureModelManager fInput;

	private SetFeatureColorAction setFeatureColorAction;
	private RemoveImportedFeatureModelsAction removeImportedFeatureModelsAction;
	private Action collapseAllAction;
	private Action expandAllAction;
	private boolean syncCollapsedFeatures = false;
	private boolean registerContextMenu = true;

	private static final String CONTEXT_MENU_ID = "de.ovgu.feautureide.fm.view.outline.contextmenu";

	public static final ImageDescriptor IMG_COLLAPSE = FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif");
	public static final ImageDescriptor IMG_EXPAND = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif");

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModelManager fInput) {
		this(site, viewer, fInput);
		this.fTextEditor = fTextEditor;
	}

	public FmOutlinePageContextMenu(Object site, TreeViewer viewer, IFeatureModelManager fInput) {
		this.site = site;
		this.viewer = viewer;
		this.fInput = fInput;
		initContextMenu();
	}

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModelManager fInput,
			boolean syncCollapsedFeatures) {
		this.site = site;
		this.fTextEditor = fTextEditor;
		this.viewer = viewer;
		this.fInput = fInput;
		this.syncCollapsedFeatures = syncCollapsedFeatures;
		initContextMenu();
	}

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModelManager fInput, boolean syncCollapsedFeatures,
			boolean registerContextMenu) {
		this.site = site;
		this.fTextEditor = fTextEditor;
		this.viewer = viewer;
		this.fInput = fInput;
		this.syncCollapsedFeatures = syncCollapsedFeatures;
		this.registerContextMenu = registerContextMenu;
		initContextMenu();
	}

	private void initContextMenu() {
		initActions();
		addListeners();
		if (registerContextMenu) {
			initMenuManager();
		}
	}

	private void initMenuManager() {
		final MenuManager menuMgr = new MenuManager("#PopupMenu");
		menuMgr.setRemoveAllWhenShown(true);
		menuMgr.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager manager) {
				FmOutlinePageContextMenu.this.fillContextMenu(manager);
			}
		});
		final Menu menu = menuMgr.createContextMenu(viewer.getControl());
		viewer.getControl().setMenu(menu);

		if (site instanceof IWorkbenchPartSite) {
			((IWorkbenchPartSite) site).registerContextMenu(CONTEXT_MENU_ID, menuMgr, viewer);
		} else {
			((IPageSite) site).registerContextMenu(CONTEXT_MENU_ID, menuMgr, viewer);
		}
	}

	private void initActions() {
		setFeatureColorAction = new SetFeatureColorAction(viewer, fInput);

		removeImportedFeatureModelsAction = new RemoveImportedFeatureModelsAction(viewer, fInput);

		collapseAllAction = new Action() {

			@Override
			public void run() {
				viewer.collapseAll();
			}
		};
		collapseAllAction.setToolTipText(COLLAPSE_ALL);
		collapseAllAction.setImageDescriptor(IMG_COLLAPSE);

		expandAllAction = new Action() {

			@Override
			public void run() {
				viewer.expandAll();
			}
		};
		expandAllAction.setToolTipText(EXPAND_ALL);
		expandAllAction.setImageDescriptor(IMG_EXPAND);

	}

	/**
	 * adds all listeners to the TreeViewer
	 */
	private void addListeners() {

		if (fTextEditor != null) {
			viewer.addSelectionChangedListener(new ISelectionChangedListener() {

				@Override
				public void selectionChanged(SelectionChangedEvent event) {
					if (viewer.getSelection() == null) {
						return;
					}

					EditPart part;
					if ((((IStructuredSelection) viewer.getSelection()).getFirstElement() instanceof IFeature)) {

						final IFeature feat = (IFeature) ((IStructuredSelection) viewer.getSelection()).getFirstElement();

						part = (EditPart) fTextEditor.diagramEditor.getViewer().getEditPartRegistry().get(feat);
					} else if ((((IStructuredSelection) viewer.getSelection()).getFirstElement() instanceof IConstraint)) {

						final IConstraint constr = (IConstraint) ((IStructuredSelection) viewer.getSelection()).getFirstElement();

						part = (EditPart) fTextEditor.diagramEditor.getViewer().getEditPartRegistry().get(constr);

					} else {
						return;
					}
					// workaround for bug: close the FM-editor and open it again,
					// -> selecting something at the outline causes a null-pointer exception
					if (part == null) {
						return;
					}
					((GraphicalViewerImpl) fTextEditor.diagramEditor.getViewer()).setSelection(new StructuredSelection(part));

					final EditPartViewer view = part.getViewer();
					if (view != null) {
						view.reveal(part);
					}
				}
			});
		}
	}

	/**
	 * fills the ContextMenu depending on the current selection
	 *
	 * @param manager given manager
	 */
	public void fillContextMenu(IMenuManager manager) {
		final ITreeSelection selection = viewer.getStructuredSelection();

		if (!selection.isEmpty() && StreamSupport.stream((Spliterator<?>) selection.spliterator(), false).allMatch(element -> element instanceof IFeature)) {
			manager.add(setFeatureColorAction);
		}
		if (!selection.isEmpty()
			&& StreamSupport.stream((Spliterator<?>) selection.spliterator(), false).allMatch(element -> element instanceof MultiFeatureModel.UsedModel)) {
			manager.add(removeImportedFeatureModelsAction);
		}
	}

	public void addToolbar(IToolBarManager iToolBarManager) {
		iToolBarManager.add(collapseAllAction);
		iToolBarManager.add(expandAllAction);
	}

	public SetFeatureColorAction getSetFeatureAction() {
		return setFeatureColorAction;
	}

	public FeatureModelEditor getFeatureModelEditor() {
		return fTextEditor;
	}

	public IManager<IFeatureModel> getFeatureModelManager() {
		return fInput;
	}

	public void setSyncCollapsedFeatures(boolean syncCollapsedFeaturesToggle) {
		syncCollapsedFeatures = syncCollapsedFeaturesToggle;
	}
}
