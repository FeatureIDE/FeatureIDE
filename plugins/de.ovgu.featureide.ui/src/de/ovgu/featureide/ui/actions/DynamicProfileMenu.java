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
package de.ovgu.featureide.ui.actions;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.internal.ui.packageview.PackageFragmentRootContainer;
import org.eclipse.jface.action.ContributionItem;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITreeSelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.internal.Workbench;

import de.ovgu.featureide.core.CorePlugin;
import de.ovgu.featureide.core.IFeatureProject;
import de.ovgu.featureide.fm.core.base.IFeatureModel;
import de.ovgu.featureide.fm.core.base.impl.FMFactoryManager;
import de.ovgu.featureide.fm.core.color.ColorScheme;
import de.ovgu.featureide.fm.core.color.FeatureColorManager;
import de.ovgu.featureide.ui.UIPlugin;

/**
 * Class to add the profilemenu to the contextmenu of the project (projectonly)
 *
 * @author Jonas Weigt
 * @author Christian Harnisch
 * @author Marcus Pinnecke
 */

@SuppressWarnings({ "restriction" })
public class DynamicProfileMenu extends ContributionItem {

	private AddProfileColorSchemeAction addProfileSchemeAction;
	private RenameProfileColorSchemeAction renameProfileSchemeAction;
	private DeleteProfileColorSchemeAction deleteProfileSchemeAction;
	private final IFeatureModel featureModel;
	{
		final IFeatureProject curFeatureProject = getCurrentFeatureProject();
		featureModel = curFeatureProject == null ? FMFactoryManager.getEmptyFeatureModel() : curFeatureProject.getFeatureModel();
	}
	private final boolean multipleSelected = isMultipleSelection();

	public DynamicProfileMenu() {}

	public DynamicProfileMenu(String id) {
		super(id);
	}

	/**
	 * Creates dynamic menu
	 */
	@Override
	public void fill(Menu menu, int index) {
		if (featureModel == null) {
			return;
		}
		final MenuManager man = new MenuManager("Color Scheme Menu", UIPlugin.getDefault().getImageDescriptor("icons/FeatureColorIcon.gif"), "");
		man.addMenuListener(new IMenuListener() {

			@Override
			public void menuAboutToShow(IMenuManager m) {
				fillContextMenu(m);
			}
		});

		if (multipleSelected == false) {
			man.fill(menu, index);
		}

		man.setVisible(true);
		createActions();
	}

	/**
	 * Fills the {@link IMenuManager} with action-buttons.
	 */
	private void fillContextMenu(IMenuManager menuMgr) {
		for (final ColorScheme cs : FeatureColorManager.getColorSchemes(featureModel)) {
			if (cs.isDefault()) {
				continue;
			}
			final SetProfileColorSchemeAction setCSAction = new SetProfileColorSchemeAction(cs.getName(), IAction.AS_CHECK_BOX, featureModel);
			if (cs.isCurrent()) {
				setCSAction.setChecked(true);
			}
			menuMgr.add(setCSAction);

		}
		menuMgr.add(new Separator());
		menuMgr.add(addProfileSchemeAction);
		menuMgr.add(renameProfileSchemeAction);
		menuMgr.add(deleteProfileSchemeAction);

		/*
		 * disables rename and delete when default colorscheme is selected
		 */
		if (FeatureColorManager.getCurrentColorScheme(featureModel).isDefault()) {
			renameProfileSchemeAction.setEnabled(false);
			deleteProfileSchemeAction.setEnabled(false);
		}

		menuMgr.setRemoveAllWhenShown(true);
	}

	/**
	 * Creates functionality of the action-buttons.
	 */
	private void createActions() {
		addProfileSchemeAction = new AddProfileColorSchemeAction("Add Color Scheme", featureModel);
		renameProfileSchemeAction = new RenameProfileColorSchemeAction("Change Name", featureModel);
		deleteProfileSchemeAction = new DeleteProfileColorSchemeAction("Delete Color Scheme", featureModel);
	}

	/**
	 * Returns selection of type IStructuredSelection
	 */
	private static IStructuredSelection getIStructuredCurrentSelection() {
		final ISelectionService selectionService = Workbench.getInstance().getActiveWorkbenchWindow().getSelectionService();

		final ISelection selection = selectionService.getSelection();
		return (IStructuredSelection) selection;
	}

	/**
	 * Disables the profilemenu, if more than one project is selected
	 */
	private static boolean isMultipleSelection() {
		final IStructuredSelection myselection = getIStructuredCurrentSelection();

		if (myselection instanceof ITreeSelection) {
			final TreeSelection treeSelection = (TreeSelection) myselection;
			final TreePath[] treePaths = treeSelection.getPaths();
			if (treePaths.length > 1) {
				return true;

			}
		}
		return false;

	}

	/**
	 * Returns selected FeatureProject
	 */
	private static IFeatureProject getCurrentFeatureProject() {
		if (getIStructuredCurrentSelection() != null) {
			final Object element = getIStructuredCurrentSelection().getFirstElement();
			if (element != null) {
				if (element instanceof IResource) {
					return CorePlugin.getFeatureProject((IResource) element);
				} else if (element instanceof PackageFragmentRootContainer) {
					final IJavaProject jProject = ((PackageFragmentRootContainer) element).getJavaProject();
					return CorePlugin.getFeatureProject(jProject.getProject());
				} else if (element instanceof IJavaElement) {
					return CorePlugin.getFeatureProject(((IJavaElement) element).getJavaProject().getProject());
				} else if (element instanceof IAdaptable) {
					// Cast is necessary, don't remove
					final IProject project = (IProject) ((IAdaptable) element).getAdapter(IProject.class);
					if (project != null) {
						return CorePlugin.getFeatureProject(project);
					}
				}
				throw new RuntimeException("element " + element + "(" + element.getClass() + ") not covered");
			}
		}
		return null;
	}

}
