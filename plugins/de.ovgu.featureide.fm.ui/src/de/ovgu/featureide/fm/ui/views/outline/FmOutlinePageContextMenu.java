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
package de.ovgu.featureide.fm.ui.views.outline;

import static de.ovgu.featureide.fm.core.localization.StringTable.COLLAPSE_ALL;
import static de.ovgu.featureide.fm.core.localization.StringTable.CONSTRAINTS;
import static de.ovgu.featureide.fm.core.localization.StringTable.CREATE_FEATURE_BELOW;
import static de.ovgu.featureide.fm.core.localization.StringTable.DELETE;
import static de.ovgu.featureide.fm.core.localization.StringTable.EXPAND_ALL;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gef.ui.parts.GraphicalViewerImpl;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.part.IPageSite;

import de.ovgu.featureide.fm.core.base.IConstraint;
import de.ovgu.featureide.fm.core.base.IFeature;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.ExtendedFeature;
import de.ovgu.featureide.fm.ui.FMUIPlugin;
import de.ovgu.featureide.fm.ui.editors.FeatureModelEditor;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AbstractAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AlternativeAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.AndAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateCompoundAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.CreateLayerAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.DeleteAllAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.EditConstraintAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.HiddenAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.MandatoryAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.OrAction;
import de.ovgu.featureide.fm.ui.editors.featuremodel.actions.colors.SetFeatureColorAction;
import de.ovgu.featureide.fm.ui.views.outline.standard.FmOutlineGroupStateStorage;

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
	private IFeatureModel fInput;

	private SetFeatureColorAction setFeatureColorAction;
	private HiddenAction hAction;
	private MandatoryAction mAction;
	private AbstractAction aAction;
	private DeleteAction dAction;
	private DeleteAllAction dAAction;
	private CreateCompoundAction cAction;
	private CreateLayerAction clAction;
	private CreateConstraintAction ccAction;
	private EditConstraintAction ecAction;
	private OrAction oAction;
	private AndAction andAction;
	private AlternativeAction altAction;
	private Action collapseAllAction;
	private Action expandAllAction;
	public IDoubleClickListener dblClickListener;
	private boolean syncCollapsedFeatures = false;
	private boolean registerContextMenu = true;

	private static final String CONTEXT_MENU_ID = "de.ovgu.feautureide.fm.view.outline.contextmenu";

	public static final ImageDescriptor IMG_COLLAPSE = FMUIPlugin.getDefault().getImageDescriptor("icons/collapse.gif");
	public static final ImageDescriptor IMG_EXPAND = FMUIPlugin.getDefault().getImageDescriptor("icons/expand.gif");

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModel fInput) {
		this(site, viewer, fInput);
		this.fTextEditor = fTextEditor;
	}

	public FmOutlinePageContextMenu(Object site, TreeViewer viewer, IFeatureModel fInput) {
		this.site = site;
		this.viewer = viewer;
		this.fInput = fInput;
		initContextMenu();
	}

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModel fInput, boolean syncCollapsedFeatures) {
		this.site = site;
		this.fTextEditor = fTextEditor;
		this.viewer = viewer;
		this.fInput = fInput;
		this.syncCollapsedFeatures = syncCollapsedFeatures;
		initContextMenu();
	}

	public FmOutlinePageContextMenu(Object site, TreeViewer viewer, IFeatureModel fInput, boolean registerContextMenu) {
		this.site = site;
		this.viewer = viewer;
		this.fInput = fInput;
		this.registerContextMenu = registerContextMenu;
		initContextMenu();
	}

	public FmOutlinePageContextMenu(Object site, FeatureModelEditor fTextEditor, TreeViewer viewer, IFeatureModel fInput, boolean syncCollapsedFeatures,
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
		mAction = new MandatoryAction(viewer, fInput);
		hAction = new HiddenAction(viewer, fInput);
		aAction = new AbstractAction(viewer, fInput);
		dAction = new DeleteAction(viewer, fInput);
		dAAction = new DeleteAllAction(viewer, fInput);
		ccAction = new CreateConstraintAction(viewer, fInput);
		ecAction = new EditConstraintAction(viewer, fInput);
		cAction = new CreateCompoundAction(viewer, fInput);
		clAction = new CreateLayerAction(viewer, fInput);
		oAction = new OrAction(viewer, fInput);
		// TODO _interfaces Removed Code
		// roAction = new ReverseOrderAction(viewer, fInput);
		andAction = new AndAction(viewer, fInput);
		altAction = new AlternativeAction(viewer, fInput);

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

		dblClickListener = new IDoubleClickListener() {

			@Override
			public void doubleClick(DoubleClickEvent event) {
				if ((((IStructuredSelection) viewer.getSelection()).getFirstElement() instanceof IFeature)) {
					if (syncCollapsedFeatures) {
						// collapseAction.run();
					} else if ((((IStructuredSelection) viewer.getSelection()).getFirstElement() instanceof IConstraint)) {
						ecAction.run();
					}
				}
			}
		};

	}

	/**
	 * adds all listeners to the TreeViewer
	 */
	private void addListeners() {
		viewer.removeDoubleClickListener(dblClickListener);
		viewer.addDoubleClickListener(dblClickListener);

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
	 * @param manager
	 */
	public void fillContextMenu(IMenuManager manager) {
		final Object sel = ((IStructuredSelection) viewer.getSelection()).getFirstElement();

		if (sel instanceof FmOutlineGroupStateStorage) {
			final IFeature feature = ((FmOutlineGroupStateStorage) sel).getFeature();
			if ((feature instanceof ExtendedFeature) && ((ExtendedFeature) feature).isFromExtern()) {
				return;
			}
			manager.add(andAction);
			manager.add(oAction);
			manager.add(altAction);
			manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
			// TODO _interfaces Removed Code
			// manager.add(roAction);
		}
		if (sel instanceof IFeature) {

			manager.add(cAction);

			clAction.setText(CREATE_FEATURE_BELOW);
			manager.add(clAction);

			dAction.setText(DELETE);
			manager.add(dAction);

			manager.add(dAAction);

			manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));

			if (oAction.isEnabled() || altAction.isEnabled() || andAction.isEnabled()) {
				manager.add(andAction);
				manager.add(oAction);
				manager.add(altAction);
				manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
			}

			manager.add(mAction);
			manager.add(aAction);
			manager.add(hAction);
			manager.add(new Separator(IWorkbenchActionConstants.MB_ADDITIONS));
			// TODO _interfaces Removed Code
			manager.add(setFeatureColorAction);
		}
		if (sel instanceof IConstraint) {
			manager.add(ccAction);
			manager.add(ecAction);

			dAction.setText(DELETE);
			manager.add(dAction);
		}
		if (sel instanceof String) {
			if (sel.equals(CONSTRAINTS)) {
				manager.add(ccAction);
			}
		}
	}

	/**
	 * @param iToolBarManager
	 */
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

	public IFeatureModel getFeatureModel() {
		return fInput;
	}

	public void setFeatureModel(IFeatureModel fm) {
		fInput = fm;
	}

	/**
	 * @param syncCollapsedFeaturesToggle
	 */
	public void setSyncCollapsedFeatures(boolean syncCollapsedFeaturesToggle) {
		syncCollapsedFeatures = syncCollapsedFeaturesToggle;
	}
}
